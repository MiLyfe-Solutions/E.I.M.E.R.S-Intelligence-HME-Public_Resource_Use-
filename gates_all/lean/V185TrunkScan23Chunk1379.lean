import V185TrunkScan23Chunk1378

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8167964 : List Nat := [2, 2, 3, 1, 2, 2, 11]
def baseStart_8167964 : Nat := 118140960795 + 8167964 * 2 ^ 59
def prefixEnd_8167964 : Nat := 4983230072969 + 3 ^ 40 * 8167964 * 2
def baseEnd_8167964 : Nat := 51778907415068963419583

theorem tailTrace_8167964 : CollatzResearch.WordTrace tailWord_8167964 prefixEnd_8167964 51778907415068963419583 := by
  unfold tailWord_8167964
  simp only [CollatzResearch.WordTrace]
  refine ⟨148955060690434440018251473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198606747587245920024335297 148955060690434440018251473)
  ·
    refine ⟨111716295517825830013688605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148955060690434440018251473 111716295517825830013688605)
    ·
      refine ⟨41893610819184686255133227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111716295517825830013688605 41893610819184686255133227)
      ·
        refine ⟨62840416228777029382699841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41893610819184686255133227 62840416228777029382699841)
        ·
          refine ⟨47130312171582772037024881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62840416228777029382699841 47130312171582772037024881)
          ·
            refine ⟨35347734128687079027768661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47130312171582772037024881 35347734128687079027768661)
            ·
              refine ⟨51778907415068963419583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 35347734128687079027768661 51778907415068963419583)
              ·
                rfl

theorem cell23_8167964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 11].length) (baseStart_8167964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167964 prefixEnd_8167964 := by exact prefixLift 8167964
  have htrace : WordTrace (prefixWord ++ tailWord_8167964) baseStart_8167964 baseEnd_8167964 := by
    simpa [prefixWord, tailWord_8167964, baseEnd_8167964] using wordTrace_append hprefix tailTrace_8167964
  have hstable : (prefixWord ++ tailWord_8167964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167964).length < 2 ^ (prefixWord ++ tailWord_8167964).sum := by decide
  have hdescent : baseEnd_8167964 < baseStart_8167964 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8167991 : List Nat := [1, 1, 3, 1, 2, 3, 2, 3, 1, 3, 3]
def baseStart_8167991 : Nat := 118140960795 + 8167991 * 2 ^ 59
def prefixEnd_8167991 : Nat := 4983230072969 + 3 ^ 40 * 8167991 * 2
def baseEnd_8167991 : Nat := 4194105364598257431348599

theorem tailTrace_8167991 : CollatzResearch.WordTrace tailWord_8167991 prefixEnd_8167991 4194105364598257431348599 := by
  unfold tailWord_8167991
  simp only [CollatzResearch.WordTrace]
  refine ⟨297911106151771063647735827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198607404101180709098490551 297911106151771063647735827)
  ·
    refine ⟨446866659227656595471603741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297911106151771063647735827 446866659227656595471603741)
    ·
      refine ⟨167574997210371223301851403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 446866659227656595471603741 167574997210371223301851403)
      ·
        refine ⟨251362495815556834952777105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167574997210371223301851403 251362495815556834952777105)
        ·
          refine ⟨188521871861667626214582829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251362495815556834952777105 188521871861667626214582829)
          ·
            refine ⟨70695701948125359830468561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188521871861667626214582829 70695701948125359830468561)
            ·
              refine ⟨53021776461094019872851421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70695701948125359830468561 53021776461094019872851421)
              ·
                refine ⟨19883166172910257452319283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53021776461094019872851421 19883166172910257452319283)
                ·
                  refine ⟨29824749259365386178478925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19883166172910257452319283 29824749259365386178478925)
                  ·
                    refine ⟨11184280972262019816929597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29824749259365386178478925 11184280972262019816929597)
                    ·
                      refine ⟨4194105364598257431348599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11184280972262019816929597 4194105364598257431348599)
                      ·
                        rfl

theorem cell23_8167991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 3, 3].length) (baseStart_8167991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8167991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8167991 prefixEnd_8167991 := by exact prefixLift 8167991
  have htrace : WordTrace (prefixWord ++ tailWord_8167991) baseStart_8167991 baseEnd_8167991 := by
    simpa [prefixWord, tailWord_8167991, baseEnd_8167991] using wordTrace_append hprefix tailTrace_8167991
  have hstable : (prefixWord ++ tailWord_8167991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8167991).length < 2 ^ (prefixWord ++ tailWord_8167991).sum := by decide
  have hdescent : baseEnd_8167991 < baseStart_8167991 := by decide
  rcases family_descends (prefixWord ++ tailWord_8167991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8168065 : List Nat := [1, 2, 4, 2, 1, 1, 2, 2, 4, 2, 2]
def baseStart_8168065 : Nat := 118140960795 + 8168065 * 2 ^ 59
def prefixEnd_8168065 : Nat := 4983230072969 + 3 ^ 40 * 8168065 * 2
def baseEnd_8168065 : Nat := 4194143362166690141823259

theorem tailTrace_8168065 : CollatzResearch.WordTrace tailWord_8168065 prefixEnd_8168065 4194143362166690141823259 := by
  unfold tailWord_8168065
  simp only [CollatzResearch.WordTrace]
  refine ⟨297913805153502974285929649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198609203435668649523953099 297913805153502974285929649)
  ·
    refine ⟨223435353865127230714447237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297913805153502974285929649 223435353865127230714447237)
    ·
      refine ⟨41894128849711355758958857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223435353865127230714447237 41894128849711355758958857)
      ·
        refine ⟨31420596637283516819219143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41894128849711355758958857 31420596637283516819219143)
        ·
          refine ⟨47130894955925275228828715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31420596637283516819219143 47130894955925275228828715)
          ·
            refine ⟨70696342433887912843243073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47130894955925275228828715 70696342433887912843243073)
            ·
              refine ⟨53022256825415934632432305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70696342433887912843243073 53022256825415934632432305)
              ·
                refine ⟨39766692619061950974324229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53022256825415934632432305 39766692619061950974324229)
                ·
                  refine ⟨7456254866074115807685793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39766692619061950974324229 7456254866074115807685793)
                  ·
                    refine ⟨5592191149555586855764345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7456254866074115807685793 5592191149555586855764345)
                    ·
                      refine ⟨4194143362166690141823259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5592191149555586855764345 4194143362166690141823259)
                      ·
                        rfl

theorem cell23_8168065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_8168065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8168065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8168065 prefixEnd_8168065 := by exact prefixLift 8168065
  have htrace : WordTrace (prefixWord ++ tailWord_8168065) baseStart_8168065 baseEnd_8168065 := by
    simpa [prefixWord, tailWord_8168065, baseEnd_8168065] using wordTrace_append hprefix tailTrace_8168065
  have hstable : (prefixWord ++ tailWord_8168065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8168065).length < 2 ^ (prefixWord ++ tailWord_8168065).sum := by decide
  have hdescent : baseEnd_8168065 < baseStart_8168065 := by decide
  rcases family_descends (prefixWord ++ tailWord_8168065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8168082 : List Nat := [3, 2, 3, 1, 2, 2, 1, 1, 4, 2, 2]
def baseStart_8168082 : Nat := 118140960795 + 8168082 * 2 ^ 59
def prefixEnd_8168082 : Nat := 4983230072969 + 3 ^ 40 * 8168082 * 2
def baseEnd_8168082 : Nat := 4194152091337816575310681

theorem tailTrace_8168082 : CollatzResearch.WordTrace tailWord_8168082 prefixEnd_8168082 4194152091337816575310681 := by
  unfold tailWord_8168082
  simp only [CollatzResearch.WordTrace]
  refine ⟨74478606298610346547324625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198609616796294257459532333 74478606298610346547324625)
  ·
    refine ⟨55858954723957759910493469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74478606298610346547324625 55858954723957759910493469)
    ·
      refine ⟨20947108021484159966435051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55858954723957759910493469 20947108021484159966435051)
      ·
        refine ⟨31420662032226239949652577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20947108021484159966435051 31420662032226239949652577)
        ·
          refine ⟨23565496524169679962239433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31420662032226239949652577 23565496524169679962239433)
          ·
            refine ⟨17674122393127259971679575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23565496524169679962239433 17674122393127259971679575)
            ·
              refine ⟨26511183589690889957519363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17674122393127259971679575 26511183589690889957519363)
              ·
                refine ⟨39766775384536334936279045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26511183589690889957519363 39766775384536334936279045)
                ·
                  refine ⟨7456270384600562800552321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39766775384536334936279045 7456270384600562800552321)
                  ·
                    refine ⟨5592202788450422100414241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7456270384600562800552321 5592202788450422100414241)
                    ·
                      refine ⟨4194152091337816575310681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5592202788450422100414241 4194152091337816575310681)
                      ·
                        rfl

theorem cell23_8168082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_8168082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8168082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8168082 prefixEnd_8168082 := by exact prefixLift 8168082
  have htrace : WordTrace (prefixWord ++ tailWord_8168082) baseStart_8168082 baseEnd_8168082 := by
    simpa [prefixWord, tailWord_8168082, baseEnd_8168082] using wordTrace_append hprefix tailTrace_8168082
  have hstable : (prefixWord ++ tailWord_8168082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8168082).length < 2 ^ (prefixWord ++ tailWord_8168082).sum := by decide
  have hdescent : baseEnd_8168082 < baseStart_8168082 := by decide
  rcases family_descends (prefixWord ++ tailWord_8168082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8168088 : List Nat := [2, 1, 2, 4, 1, 1, 1, 6, 5]
def baseStart_8168088 : Nat := 118140960795 + 8168088 * 2 ^ 59
def prefixEnd_8168088 : Nat := 4983230072969 + 3 ^ 40 * 8168088 * 2
def baseEnd_8168088 : Nat := 466017241357971505759517

theorem tailTrace_8168088 : CollatzResearch.WordTrace tailWord_8168088 prefixEnd_8168088 466017241357971505759517 := by
  unfold tailWord_8168088
  simp only [CollatzResearch.WordTrace]
  refine ⟨148957322016209824607008459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198609762688279766142677945 148957322016209824607008459)
  ·
    refine ⟨223435983024314736910512689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148957322016209824607008459 223435983024314736910512689)
    ·
      refine ⟨167576987268236052682884517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223435983024314736910512689 167576987268236052682884517)
      ·
        refine ⟨31420685112794259878040847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167576987268236052682884517 31420685112794259878040847)
        ·
          refine ⟨47131027669191389817061271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31420685112794259878040847 47131027669191389817061271)
          ·
            refine ⟨70696541503787084725591907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47131027669191389817061271 70696541503787084725591907)
            ·
              refine ⟨106044812255680627088387861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70696541503787084725591907 106044812255680627088387861)
              ·
                refine ⟨4970850574485029394768181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 106044812255680627088387861 4970850574485029394768181)
                ·
                  refine ⟨466017241357971505759517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4970850574485029394768181 466017241357971505759517)
                  ·
                    rfl

theorem cell23_8168088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 6, 5].length) (baseStart_8168088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8168088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8168088 prefixEnd_8168088 := by exact prefixLift 8168088
  have htrace : WordTrace (prefixWord ++ tailWord_8168088) baseStart_8168088 baseEnd_8168088 := by
    simpa [prefixWord, tailWord_8168088, baseEnd_8168088] using wordTrace_append hprefix tailTrace_8168088
  have hstable : (prefixWord ++ tailWord_8168088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8168088).length < 2 ^ (prefixWord ++ tailWord_8168088).sum := by decide
  have hdescent : baseEnd_8168088 < baseStart_8168088 := by decide
  rcases family_descends (prefixWord ++ tailWord_8168088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8168138 : List Nat := [3, 1, 2, 1, 4, 1, 1, 1, 4, 1, 4]
def baseStart_8168138 : Nat := 118140960795 + 8168138 * 2 ^ 59
def prefixEnd_8168138 : Nat := 4983230072969 + 3 ^ 40 * 8168138 * 2
def baseEnd_8168138 : Nat := 4194180846254468356210423

theorem tailTrace_8168138 : CollatzResearch.WordTrace tailWord_8168138 prefixEnd_8168138 4194180846254468356210423 := by
  unfold tailWord_8168138
  simp only [CollatzResearch.WordTrace]
  refine ⟨74479116920559626938334267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198610978454825671835558045 74479116920559626938334267)
  ·
    refine ⟨111718675380839440407501401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74479116920559626938334267 111718675380839440407501401)
    ·
      refine ⟨83789006535629580305626051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111718675380839440407501401 83789006535629580305626051)
      ·
        refine ⟨125683509803444370458439077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83789006535629580305626051 125683509803444370458439077)
        ·
          refine ⟨23565658088145819460957327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125683509803444370458439077 23565658088145819460957327)
          ·
            refine ⟨35348487132218729191435991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23565658088145819460957327 35348487132218729191435991)
            ·
              refine ⟨53022730698328093787153987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35348487132218729191435991 53022730698328093787153987)
              ·
                refine ⟨79534096047492140680730981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53022730698328093787153987 79534096047492140680730981)
                ·
                  refine ⟨14912643008904776377637059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79534096047492140680730981 14912643008904776377637059)
                  ·
                    refine ⟨22368964513357164566455589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14912643008904776377637059 22368964513357164566455589)
                    ·
                      refine ⟨4194180846254468356210423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22368964513357164566455589 4194180846254468356210423)
                      ·
                        rfl

theorem cell23_8168138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_8168138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8168138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8168138 prefixEnd_8168138 := by exact prefixLift 8168138
  have htrace : WordTrace (prefixWord ++ tailWord_8168138) baseStart_8168138 baseEnd_8168138 := by
    simpa [prefixWord, tailWord_8168138, baseEnd_8168138] using wordTrace_append hprefix tailTrace_8168138
  have hstable : (prefixWord ++ tailWord_8168138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8168138).length < 2 ^ (prefixWord ++ tailWord_8168138).sum := by decide
  have hdescent : baseEnd_8168138 < baseStart_8168138 := by decide
  rcases family_descends (prefixWord ++ tailWord_8168138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8168175 : List Nat := [1, 1, 2, 1, 5, 3, 2, 1, 2, 2, 3]
def baseStart_8168175 : Nat := 118140960795 + 8168175 * 2 ^ 59
def prefixEnd_8168175 : Nat := 4983230072969 + 3 ^ 40 * 8168175 * 2
def baseEnd_8168175 : Nat := 4194199845038684711447753

theorem tailTrace_8168175 : CollatzResearch.WordTrace tailWord_8168175 prefixEnd_8168175 4194199845038684711447753 := by
  unfold tailWord_8168175
  simp only [CollatzResearch.WordTrace]
  refine ⟨297917817183104463072433979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198611878122069642048289319 297917817183104463072433979)
  ·
    refine ⟨446876725774656694608650969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297917817183104463072433979 446876725774656694608650969)
    ·
      refine ⟨335157544330992520956488227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446876725774656694608650969 335157544330992520956488227)
      ·
        refine ⟨502736316496488781434732341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335157544330992520956488227 502736316496488781434732341)
        ·
          refine ⟨47131529671545823259506157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 502736316496488781434732341 47131529671545823259506157)
          ·
            refine ⟨17674323626829683722314809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47131529671545823259506157 17674323626829683722314809)
            ·
              refine ⟨13255742720122262791736107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17674323626829683722314809 13255742720122262791736107)
              ·
                refine ⟨19883614080183394187604161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13255742720122262791736107 19883614080183394187604161)
                ·
                  refine ⟨14912710560137545640703121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19883614080183394187604161 14912710560137545640703121)
                  ·
                    refine ⟨11184532920103159230527341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14912710560137545640703121 11184532920103159230527341)
                    ·
                      refine ⟨4194199845038684711447753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11184532920103159230527341 4194199845038684711447753)
                      ·
                        rfl

theorem cell23_8168175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 2, 2, 3].length) (baseStart_8168175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8168175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8168175 prefixEnd_8168175 := by exact prefixLift 8168175
  have htrace : WordTrace (prefixWord ++ tailWord_8168175) baseStart_8168175 baseEnd_8168175 := by
    simpa [prefixWord, tailWord_8168175, baseEnd_8168175] using wordTrace_append hprefix tailTrace_8168175
  have hstable : (prefixWord ++ tailWord_8168175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8168175).length < 2 ^ (prefixWord ++ tailWord_8168175).sum := by decide
  have hdescent : baseEnd_8168175 < baseStart_8168175 := by decide
  rcases family_descends (prefixWord ++ tailWord_8168175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8168182 : List Nat := [5, 1, 1, 1, 1, 2, 2, 5, 1, 4]
def baseStart_8168182 : Nat := 118140960795 + 8168182 * 2 ^ 59
def prefixEnd_8168182 : Nat := 4983230072969 + 3 ^ 40 * 8168182 * 2
def baseEnd_8168182 : Nat := 1398067813134422061353407

theorem tailTrace_8168182 : CollatzResearch.WordTrace tailWord_8168182 prefixEnd_8168182 1398067813134422061353407 := by
  unfold tailWord_8168182
  simp only [CollatzResearch.WordTrace]
  refine ⟨18619879530879943954246175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198612048329386068845292533 18619879530879943954246175)
  ·
    refine ⟨27929819296319915931369263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18619879530879943954246175 27929819296319915931369263)
    ·
      refine ⟨41894728944479873897053895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27929819296319915931369263 41894728944479873897053895)
      ·
        refine ⟨62842093416719810845580843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41894728944479873897053895 62842093416719810845580843)
        ·
          refine ⟨94263140125079716268371265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62842093416719810845580843 94263140125079716268371265)
          ·
            refine ⟨70697355093809787201278449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94263140125079716268371265 70697355093809787201278449)
            ·
              refine ⟨53023016320357340400958837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70697355093809787201278449 53023016320357340400958837)
              ·
                refine ⟨4970907780033500662589891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53023016320357340400958837 4970907780033500662589891)
                ·
                  refine ⟨7456361670050250993884837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4970907780033500662589891 7456361670050250993884837)
                  ·
                    refine ⟨1398067813134422061353407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7456361670050250993884837 1398067813134422061353407)
                    ·
                      rfl

theorem cell23_8168182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_8168182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8168182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8168182 prefixEnd_8168182 := by exact prefixLift 8168182
  have htrace : WordTrace (prefixWord ++ tailWord_8168182) baseStart_8168182 baseEnd_8168182 := by
    simpa [prefixWord, tailWord_8168182, baseEnd_8168182] using wordTrace_append hprefix tailTrace_8168182
  have hstable : (prefixWord ++ tailWord_8168182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8168182).length < 2 ^ (prefixWord ++ tailWord_8168182).sum := by decide
  have hdescent : baseEnd_8168182 < baseStart_8168182 := by decide
  rcases family_descends (prefixWord ++ tailWord_8168182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8168199 : List Nat := [1, 1, 4, 4, 1, 1, 4, 2, 1, 4]
def baseStart_8168199 : Nat := 118140960795 + 8168199 * 2 ^ 59
def prefixEnd_8168199 : Nat := 4983230072969 + 3 ^ 40 * 8168199 * 2
def baseEnd_8168199 : Nat := 1398070722858130872515881

theorem tailTrace_8168199 : CollatzResearch.WordTrace tailWord_8168199 prefixEnd_8168199 1398070722858130872515881 := by
  unfold tailWord_8168199
  simp only [CollatzResearch.WordTrace]
  refine ⟨297918692535017515171307651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198612461690011676780871767 297918692535017515171307651)
  ·
    refine ⟨446878038802526272756961477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297918692535017515171307651 446878038802526272756961477)
    ·
      refine ⟨83789632275473676141930277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 446878038802526272756961477 83789632275473676141930277)
      ·
        refine ⟨15710556051651314276611927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83789632275473676141930277 15710556051651314276611927)
        ·
          refine ⟨23565834077476971414917891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15710556051651314276611927 23565834077476971414917891)
          ·
            refine ⟨35348751116215457122376837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23565834077476971414917891 35348751116215457122376837)
            ·
              refine ⟨6627890834290398210445657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35348751116215457122376837 6627890834290398210445657)
              ·
                refine ⟨4970918125717798657834243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6627890834290398210445657 4970918125717798657834243)
                ·
                  refine ⟨7456377188576697986751365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4970918125717798657834243 7456377188576697986751365)
                  ·
                    refine ⟨1398070722858130872515881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7456377188576697986751365 1398070722858130872515881)
                    ·
                      rfl

theorem cell23_8168199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 2, 1, 4].length) (baseStart_8168199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8168199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8168199 prefixEnd_8168199 := by exact prefixLift 8168199
  have htrace : WordTrace (prefixWord ++ tailWord_8168199) baseStart_8168199 baseEnd_8168199 := by
    simpa [prefixWord, tailWord_8168199, baseEnd_8168199] using wordTrace_append hprefix tailTrace_8168199
  have hstable : (prefixWord ++ tailWord_8168199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8168199).length < 2 ^ (prefixWord ++ tailWord_8168199).sum := by decide
  have hdescent : baseEnd_8168199 < baseStart_8168199 := by decide
  rcases family_descends (prefixWord ++ tailWord_8168199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8168248 : List Nat := [2, 1, 2, 1, 3, 2, 2, 3, 1, 1, 5]
def baseStart_8168248 : Nat := 118140960795 + 8168248 * 2 ^ 59
def prefixEnd_8168248 : Nat := 4983230072969 + 3 ^ 40 * 8168248 * 2
def baseEnd_8168248 : Nat := 4194237329126462925834917

theorem tailTrace_8168248 : CollatzResearch.WordTrace tailWord_8168248 prefixEnd_8168248 4194237329126462925834917 := by
  unfold tailWord_8168248
  simp only [CollatzResearch.WordTrace]
  refine ⟨148960239855919998269920699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198613653141226664359894265 148960239855919998269920699)
  ·
    refine ⟨223440359783879997404881049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148960239855919998269920699 223440359783879997404881049)
    ·
      refine ⟨167580269837909998053660787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223440359783879997404881049 167580269837909998053660787)
      ·
        refine ⟨251370404756864997080491181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167580269837909998053660787 251370404756864997080491181)
        ·
          refine ⟨94263901783824373905184193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251370404756864997080491181 94263901783824373905184193)
          ·
            refine ⟨70697926337868280428888145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94263901783824373905184193 70697926337868280428888145)
            ·
              refine ⟨53023444753401210321666109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70697926337868280428888145 53023444753401210321666109)
              ·
                refine ⟨19883791782525453870624791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53023444753401210321666109 19883791782525453870624791)
                ·
                  refine ⟨29825687673788180805937187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19883791782525453870624791 29825687673788180805937187)
                  ·
                    refine ⟨44738531510682271208905781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29825687673788180805937187 44738531510682271208905781)
                    ·
                      refine ⟨4194237329126462925834917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44738531510682271208905781 4194237329126462925834917)
                      ·
                        rfl

theorem cell23_8168248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 1, 1, 5].length) (baseStart_8168248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8168248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8168248 prefixEnd_8168248 := by exact prefixLift 8168248
  have htrace : WordTrace (prefixWord ++ tailWord_8168248) baseStart_8168248 baseEnd_8168248 := by
    simpa [prefixWord, tailWord_8168248, baseEnd_8168248] using wordTrace_append hprefix tailTrace_8168248
  have hstable : (prefixWord ++ tailWord_8168248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8168248).length < 2 ^ (prefixWord ++ tailWord_8168248).sum := by decide
  have hdescent : baseEnd_8168248 < baseStart_8168248 := by decide
  rcases family_descends (prefixWord ++ tailWord_8168248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8168255 : List Nat := [1, 1, 2, 2, 5, 2, 1, 1, 4, 4]
def baseStart_8168255 : Nat := 118140960795 + 8168255 * 2 ^ 59
def prefixEnd_8168255 : Nat := 4983230072969 + 3 ^ 40 * 8168255 * 2
def baseEnd_8168255 : Nat := 1398080307830348132815795

theorem tailTrace_8168255 : CollatzResearch.WordTrace tailWord_8168255 prefixEnd_8168255 1398080307830348132815795 := by
  unfold tailWord_8168255
  simp only [CollatzResearch.WordTrace]
  refine ⟨297920735022814636735346219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198613823348543091156897479 297920735022814636735346219)
  ·
    refine ⟨446881102534221955103019329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297920735022814636735346219 446881102534221955103019329)
    ·
      refine ⟨335160826900666466327264497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446881102534221955103019329 335160826900666466327264497)
      ·
        refine ⟨251370620175499849745448373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335160826900666466327264497 251370620175499849745448373)
        ·
          refine ⟨23565995641453110913635785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 251370620175499849745448373 23565995641453110913635785)
          ·
            refine ⟨17674496731089833185226839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23565995641453110913635785 17674496731089833185226839)
            ·
              refine ⟨26511745096634749777840259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17674496731089833185226839 26511745096634749777840259)
              ·
                refine ⟨39767617644952124666760389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26511745096634749777840259 39767617644952124666760389)
                ·
                  refine ⟨7456428308428523375017573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39767617644952124666760389 7456428308428523375017573)
                  ·
                    refine ⟨1398080307830348132815795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7456428308428523375017573 1398080307830348132815795)
                    ·
                      rfl

theorem cell23_8168255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 4, 4].length) (baseStart_8168255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8168255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8168255 prefixEnd_8168255 := by exact prefixLift 8168255
  have htrace : WordTrace (prefixWord ++ tailWord_8168255) baseStart_8168255 baseEnd_8168255 := by
    simpa [prefixWord, tailWord_8168255, baseEnd_8168255] using wordTrace_append hprefix tailTrace_8168255
  have hstable : (prefixWord ++ tailWord_8168255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8168255).length < 2 ^ (prefixWord ++ tailWord_8168255).sum := by decide
  have hdescent : baseEnd_8168255 < baseStart_8168255 := by decide
  rcases family_descends (prefixWord ++ tailWord_8168255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8168282 : List Nat := [3, 1, 1, 2, 1, 5, 2, 2, 1, 2, 3]
def baseStart_8168282 : Nat := 118140960795 + 8168282 * 2 ^ 59
def prefixEnd_8168282 : Nat := 4983230072969 + 3 ^ 40 * 8168282 * 2
def baseEnd_8168282 : Nat := 4194254787468715792809761

theorem tailTrace_8168282 : CollatzResearch.WordTrace tailWord_8168282 prefixEnd_8168282 4194254787468715792809761 := by
  unfold tailWord_8168282
  simp only [CollatzResearch.WordTrace]
  refine ⟨74480429948429205086644775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198614479862477880231052733 74480429948429205086644775)
  ·
    refine ⟨111720644922643807629967163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74480429948429205086644775 111720644922643807629967163)
    ·
      refine ⟨167580967383965711444950745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111720644922643807629967163 167580967383965711444950745)
      ·
        refine ⟨125685725537974283583713059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167580967383965711444950745 125685725537974283583713059)
        ·
          refine ⟨188528588306961425375569589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125685725537974283583713059 188528588306961425375569589)
          ·
            refine ⟨17674555153777633628959649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 188528588306961425375569589 17674555153777633628959649)
            ·
              refine ⟨13255916365333225221719737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17674555153777633628959649 13255916365333225221719737)
              ·
                refine ⟨9941937273999918916289803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13255916365333225221719737 9941937273999918916289803)
                ·
                  refine ⟨14912905910999878374434705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9941937273999918916289803 14912905910999878374434705)
                  ·
                    refine ⟨11184679433249908780826029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14912905910999878374434705 11184679433249908780826029)
                    ·
                      refine ⟨4194254787468715792809761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11184679433249908780826029 4194254787468715792809761)
                      ·
                        rfl

theorem cell23_8168282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2, 1, 2, 3].length) (baseStart_8168282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8168282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8168282 prefixEnd_8168282 := by exact prefixLift 8168282
  have htrace : WordTrace (prefixWord ++ tailWord_8168282) baseStart_8168282 baseEnd_8168282 := by
    simpa [prefixWord, tailWord_8168282, baseEnd_8168282] using wordTrace_append hprefix tailTrace_8168282
  have hstable : (prefixWord ++ tailWord_8168282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8168282).length < 2 ^ (prefixWord ++ tailWord_8168282).sum := by decide
  have hdescent : baseEnd_8168282 < baseStart_8168282 := by decide
  rcases family_descends (prefixWord ++ tailWord_8168282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8168296 : List Nat := [2, 1, 4, 2, 1, 2, 3, 3, 1, 2, 2]
def baseStart_8168296 : Nat := 118140960795 + 8168296 * 2 ^ 59
def prefixEnd_8168296 : Nat := 4983230072969 + 3 ^ 40 * 8168296 * 2
def baseEnd_8168296 : Nat := 4194261976197878738034697

theorem tailTrace_8168296 : CollatzResearch.WordTrace tailWord_8168296 prefixEnd_8168296 4194261976197878738034697 := by
  unfold tailWord_8168296
  simp only [CollatzResearch.WordTrace]
  refine ⟨148961115207833050368794371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198614820277110733825059161 148961115207833050368794371)
  ·
    refine ⟨223441672811749575553191557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148961115207833050368794371 223441672811749575553191557)
    ·
      refine ⟨41895313652203045416223417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223441672811749575553191557 41895313652203045416223417)
      ·
        refine ⟨31421485239152284062167563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41895313652203045416223417 31421485239152284062167563)
        ·
          refine ⟨47132227858728426093251345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31421485239152284062167563 47132227858728426093251345)
          ·
            refine ⟨35349170894046319569938509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47132227858728426093251345 35349170894046319569938509)
            ·
              refine ⟨13255939085267369838726941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35349170894046319569938509 13255939085267369838726941)
              ·
                refine ⟨4970977156975263689522603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13255939085267369838726941 4970977156975263689522603)
                ·
                  refine ⟨7456465735462895534283905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4970977156975263689522603 7456465735462895534283905)
                  ·
                    refine ⟨5592349301597171650712929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7456465735462895534283905 5592349301597171650712929)
                    ·
                      refine ⟨4194261976197878738034697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5592349301597171650712929 4194261976197878738034697)
                      ·
                        rfl

theorem cell23_8168296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_8168296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8168296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8168296 prefixEnd_8168296 := by exact prefixLift 8168296
  have htrace : WordTrace (prefixWord ++ tailWord_8168296) baseStart_8168296 baseEnd_8168296 := by
    simpa [prefixWord, tailWord_8168296, baseEnd_8168296] using wordTrace_append hprefix tailTrace_8168296
  have hstable : (prefixWord ++ tailWord_8168296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8168296).length < 2 ^ (prefixWord ++ tailWord_8168296).sum := by decide
  have hdescent : baseEnd_8168296 < baseStart_8168296 := by decide
  rcases family_descends (prefixWord ++ tailWord_8168296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8168302 : List Nat := [4, 1, 2, 3, 3, 1, 9]
def baseStart_8168302 : Nat := 118140960795 + 8168302 * 2 ^ 59
def prefixEnd_8168302 : Nat := 4983230072969 + 3 ^ 40 * 8168302 * 2
def baseEnd_8168302 : Nat := 51781050087429700179749

theorem tailTrace_8168302 : CollatzResearch.WordTrace tailWord_8168302 prefixEnd_8168302 51781050087429700179749 := by
  unfold tailWord_8168302
  simp only [CollatzResearch.WordTrace]
  refine ⟨37240306156705545470288395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198614966169096242508204773 37240306156705545470288395)
  ·
    refine ⟨55860459235058318205432593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37240306156705545470288395 55860459235058318205432593)
    ·
      refine ⟨41895344426293738654074445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55860459235058318205432593 41895344426293738654074445)
      ·
        refine ⟨15710754159860151995277917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41895344426293738654074445 15710754159860151995277917)
        ·
          refine ⟨5891532809947556998229219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15710754159860151995277917 5891532809947556998229219)
          ·
            refine ⟨8837299214921335497343829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5891532809947556998229219 8837299214921335497343829)
            ·
              refine ⟨51781050087429700179749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8837299214921335497343829 51781050087429700179749)
              ·
                rfl

theorem cell23_8168302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 9].length) (baseStart_8168302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8168302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8168302 prefixEnd_8168302 := by exact prefixLift 8168302
  have htrace : WordTrace (prefixWord ++ tailWord_8168302) baseStart_8168302 baseEnd_8168302 := by
    simpa [prefixWord, tailWord_8168302, baseEnd_8168302] using wordTrace_append hprefix tailTrace_8168302
  have hstable : (prefixWord ++ tailWord_8168302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8168302).length < 2 ^ (prefixWord ++ tailWord_8168302).sum := by decide
  have hdescent : baseEnd_8168302 < baseStart_8168302 := by decide
  rcases family_descends (prefixWord ++ tailWord_8168302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8168329 : List Nat := [1, 2, 1, 1, 5, 2, 4, 1, 2, 1, 3]
def baseStart_8168329 : Nat := 118140960795 + 8168329 * 2 ^ 59
def prefixEnd_8168329 : Nat := 4983230072969 + 3 ^ 40 * 8168329 * 2
def baseEnd_8168329 : Nat := 4194278921059477108922045

theorem tailTrace_8168329 : CollatzResearch.WordTrace tailWord_8168329 prefixEnd_8168329 4194278921059477108922045 := by
  unfold tailWord_8168329
  simp only [CollatzResearch.WordTrace]
  refine ⟨297923434024546547373540041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198615622683031031582360027 297923434024546547373540041)
  ·
    refine ⟨223442575518409910530155031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297923434024546547373540041 223442575518409910530155031)
    ·
      refine ⟨335163863277614865795232547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223442575518409910530155031 335163863277614865795232547)
      ·
        refine ⟨502745794916422298692848821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335163863277614865795232547 502745794916422298692848821)
        ·
          refine ⟨47132418273414590502454577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 502745794916422298692848821 47132418273414590502454577)
          ·
            refine ⟨35349313705060942876840933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47132418273414590502454577 35349313705060942876840933)
            ·
              refine ⟨6627996319698926789407675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35349313705060942876840933 6627996319698926789407675)
              ·
                refine ⟨9941994479548390184111513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6627996319698926789407675 9941994479548390184111513)
                ·
                  refine ⟨7456495859661292638083635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9941994479548390184111513 7456495859661292638083635)
                  ·
                    refine ⟨11184743789491938957125453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7456495859661292638083635 11184743789491938957125453)
                    ·
                      refine ⟨4194278921059477108922045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11184743789491938957125453 4194278921059477108922045)
                      ·
                        rfl

theorem cell23_8168329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 1, 2, 1, 3].length) (baseStart_8168329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8168329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8168329 prefixEnd_8168329 := by exact prefixLift 8168329
  have htrace : WordTrace (prefixWord ++ tailWord_8168329) baseStart_8168329 baseEnd_8168329 := by
    simpa [prefixWord, tailWord_8168329, baseEnd_8168329] using wordTrace_append hprefix tailTrace_8168329
  have hstable : (prefixWord ++ tailWord_8168329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8168329).length < 2 ^ (prefixWord ++ tailWord_8168329).sum := by decide
  have hdescent : baseEnd_8168329 < baseStart_8168329 := by decide
  rcases family_descends (prefixWord ++ tailWord_8168329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8168352 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 6, 2, 2]
def baseStart_8168352 : Nat := 118140960795 + 8168352 * 2 ^ 59
def prefixEnd_8168352 : Nat := 4983230072969 + 3 ^ 40 * 8168352 * 2
def baseEnd_8168352 : Nat := 4194290731114530518934439

theorem tailTrace_8168352 : CollatzResearch.WordTrace tailWord_8168352 prefixEnd_8168352 4194290731114530518934439 := by
  unfold tailWord_8168352
  simp only [CollatzResearch.WordTrace]
  refine ⟨148962136451731611150813655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198616181935642148201084873 148962136451731611150813655)
  ·
    refine ⟨223443204677597416726220483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148962136451731611150813655 223443204677597416726220483)
    ·
      refine ⟨335164807016396125089330725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223443204677597416726220483 335164807016396125089330725)
      ·
        refine ⟨62843401315574273454249511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 335164807016396125089330725 62843401315574273454249511)
        ·
          refine ⟨94265101973361410181374267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62843401315574273454249511 94265101973361410181374267)
          ·
            refine ⟨141397652960042115272061401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94265101973361410181374267 141397652960042115272061401)
            ·
              refine ⟨106048239720031586454046051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141397652960042115272061401 106048239720031586454046051)
              ·
                refine ⟨159072359580047379681069077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106048239720031586454046051 159072359580047379681069077)
                ·
                  refine ⟨7456516855314720922550113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 159072359580047379681069077 7456516855314720922550113)
                  ·
                    refine ⟨5592387641486040691912585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7456516855314720922550113 5592387641486040691912585)
                    ·
                      refine ⟨4194290731114530518934439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5592387641486040691912585 4194290731114530518934439)
                      ·
                        rfl

theorem cell23_8168352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 6, 2, 2].length) (baseStart_8168352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8168352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8168352 prefixEnd_8168352 := by exact prefixLift 8168352
  have htrace : WordTrace (prefixWord ++ tailWord_8168352) baseStart_8168352 baseEnd_8168352 := by
    simpa [prefixWord, tailWord_8168352, baseEnd_8168352] using wordTrace_append hprefix tailTrace_8168352
  have hstable : (prefixWord ++ tailWord_8168352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8168352).length < 2 ^ (prefixWord ++ tailWord_8168352).sum := by decide
  have hdescent : baseEnd_8168352 < baseStart_8168352 := by decide
  rcases family_descends (prefixWord ++ tailWord_8168352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8168455 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 2, 4, 4]
def baseStart_8168455 : Nat := 118140960795 + 8168455 * 2 ^ 59
def prefixEnd_8168455 : Nat := 4983230072969 + 3 ^ 40 * 8168455 * 2
def baseEnd_8168455 : Nat := 4194343619621943615946465

theorem tailTrace_8168455 : CollatzResearch.WordTrace tailWord_8168455 prefixEnd_8168455 4194343619621943615946465 := by
  unfold tailWord_8168455
  simp only [CollatzResearch.WordTrace]
  refine ⟨297928029622090070892626819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198618686414726713928417879 297928029622090070892626819)
  ·
    refine ⟨446892044433135106338940229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297928029622090070892626819 446892044433135106338940229)
    ·
      refine ⟨83792258331212832438551293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 446892044433135106338940229 83792258331212832438551293)
      ·
        refine ⟨31422096874204812164456735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83792258331212832438551293 31422096874204812164456735)
        ·
          refine ⟨47133145311307218246685103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31422096874204812164456735 47133145311307218246685103)
          ·
            refine ⟨70699717966960827370027655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47133145311307218246685103 70699717966960827370027655)
            ·
              refine ⟨106049576950441241055041483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70699717966960827370027655 106049576950441241055041483)
              ·
                refine ⟨159074365425661861582562225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106049576950441241055041483 159074365425661861582562225)
                ·
                  refine ⟨119305774069246396186921669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159074365425661861582562225 119305774069246396186921669)
                  ·
                    refine ⟨22369832637983699285047813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 119305774069246396186921669 22369832637983699285047813)
                    ·
                      refine ⟨4194343619621943615946465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22369832637983699285047813 4194343619621943615946465)
                      ·
                        rfl

theorem cell23_8168455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_8168455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8168455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8168455 prefixEnd_8168455 := by exact prefixLift 8168455
  have htrace : WordTrace (prefixWord ++ tailWord_8168455) baseStart_8168455 baseEnd_8168455 := by
    simpa [prefixWord, tailWord_8168455, baseEnd_8168455] using wordTrace_append hprefix tailTrace_8168455
  have hstable : (prefixWord ++ tailWord_8168455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8168455).length < 2 ^ (prefixWord ++ tailWord_8168455).sum := by decide
  have hdescent : baseEnd_8168455 < baseStart_8168455 := by decide
  rcases family_descends (prefixWord ++ tailWord_8168455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8168462 : List Nat := [4, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3]
def baseStart_8168462 : Nat := 118140960795 + 8168462 * 2 ^ 59
def prefixEnd_8168462 : Nat := 4983230072969 + 3 ^ 40 * 8168462 * 2
def baseEnd_8168462 : Nat := 4194347213986525088558933

theorem tailTrace_8168462 : CollatzResearch.WordTrace tailWord_8168462 prefixEnd_8168462 4194347213986525088558933 := by
  unfold tailWord_8168462
  simp only [CollatzResearch.WordTrace]
  refine ⟨37241035616633088886016455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198618856622043140725421093 37241035616633088886016455)
  ·
    refine ⟨55861553424949633329024683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37241035616633088886016455 55861553424949633329024683)
    ·
      refine ⟨83792330137424449993537025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55861553424949633329024683 83792330137424449993537025)
      ·
        refine ⟨62844247603068337495152769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83792330137424449993537025 62844247603068337495152769)
        ·
          refine ⟨47133185702301253121364577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62844247603068337495152769 47133185702301253121364577)
          ·
            refine ⟨35349889276725939841023433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47133185702301253121364577 35349889276725939841023433)
            ·
              refine ⟨26512416957544454880767575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35349889276725939841023433 26512416957544454880767575)
              ·
                refine ⟨39768625436316682321151363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26512416957544454880767575 39768625436316682321151363)
                ·
                  refine ⟨59652938154475023481727045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39768625436316682321151363 59652938154475023481727045)
                  ·
                    refine ⟨11184925903964066902823821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59652938154475023481727045 11184925903964066902823821)
                    ·
                      refine ⟨4194347213986525088558933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11184925903964066902823821 4194347213986525088558933)
                      ·
                        rfl

theorem cell23_8168462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_8168462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8168462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8168462 prefixEnd_8168462 := by exact prefixLift 8168462
  have htrace : WordTrace (prefixWord ++ tailWord_8168462) baseStart_8168462 baseEnd_8168462 := by
    simpa [prefixWord, tailWord_8168462, baseEnd_8168462] using wordTrace_append hprefix tailTrace_8168462
  have hstable : (prefixWord ++ tailWord_8168462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8168462).length < 2 ^ (prefixWord ++ tailWord_8168462).sum := by decide
  have hdescent : baseEnd_8168462 < baseStart_8168462 := by decide
  rcases family_descends (prefixWord ++ tailWord_8168462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8168519 : List Nat := [1, 1, 4, 1, 3, 2, 1, 3, 2, 3, 2]
def baseStart_8168519 : Nat := 118140960795 + 8168519 * 2 ^ 59
def prefixEnd_8168519 : Nat := 4983230072969 + 3 ^ 40 * 8168519 * 2
def baseEnd_8168519 : Nat := 4194376482383831365546171

theorem tailTrace_8168519 : CollatzResearch.WordTrace tailWord_8168519 prefixEnd_8168519 4194376482383831365546171 := by
  unfold tailWord_8168519
  simp only [CollatzResearch.WordTrace]
  refine ⟨297930363893858209822956611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198620242595905473215304407 297930363893858209822956611)
  ·
    refine ⟨446895545840787314734434917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297930363893858209822956611 446895545840787314734434917)
    ·
      refine ⟨83792914845147621512706547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 446895545840787314734434917 83792914845147621512706547)
      ·
        refine ⟨125689372267721432269059821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83792914845147621512706547 125689372267721432269059821)
        ·
          refine ⟨47133514600395537100897433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125689372267721432269059821 47133514600395537100897433)
          ·
            refine ⟨35350135950296652825673075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47133514600395537100897433 35350135950296652825673075)
            ·
              refine ⟨53025203925444979238509613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35350135950296652825673075 53025203925444979238509613)
              ·
                refine ⟨19884451472041867214441105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53025203925444979238509613 19884451472041867214441105)
                ·
                  refine ⟨14913338604031400410830829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19884451472041867214441105 14913338604031400410830829)
                  ·
                    refine ⟨5592501976511775154061561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14913338604031400410830829 5592501976511775154061561)
                    ·
                      refine ⟨4194376482383831365546171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5592501976511775154061561 4194376482383831365546171)
                      ·
                        rfl

theorem cell23_8168519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2, 3, 2].length) (baseStart_8168519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8168519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8168519 prefixEnd_8168519 := by exact prefixLift 8168519
  have htrace : WordTrace (prefixWord ++ tailWord_8168519) baseStart_8168519 baseEnd_8168519 := by
    simpa [prefixWord, tailWord_8168519, baseEnd_8168519] using wordTrace_append hprefix tailTrace_8168519
  have hstable : (prefixWord ++ tailWord_8168519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8168519).length < 2 ^ (prefixWord ++ tailWord_8168519).sum := by decide
  have hdescent : baseEnd_8168519 < baseStart_8168519 := by decide
  rcases family_descends (prefixWord ++ tailWord_8168519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8168526 : List Nat := [4, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3]
def baseStart_8168526 : Nat := 118140960795 + 8168526 * 2 ^ 59
def prefixEnd_8168526 : Nat := 4983230072969 + 3 ^ 40 * 8168526 * 2
def baseEnd_8168526 : Nat := 4194380076748412838158639

theorem tailTrace_8168526 : CollatzResearch.WordTrace tailWord_8168526 prefixEnd_8168526 4194380076748412838158639 := by
  unfold tailWord_8168526
  simp only [CollatzResearch.WordTrace]
  refine ⟨37241327400604106252307679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198620412803221900012307621 37241327400604106252307679)
  ·
    refine ⟨55861991100906159378461519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37241327400604106252307679 55861991100906159378461519)
    ·
      refine ⟨83792986651359239067692279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55861991100906159378461519 83792986651359239067692279)
      ·
        refine ⟨125689479977038858601538419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83792986651359239067692279 125689479977038858601538419)
        ·
          refine ⟨188534219965558287902307629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125689479977038858601538419 188534219965558287902307629)
          ·
            refine ⟨70700332487084357963365361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188534219965558287902307629 70700332487084357963365361)
            ·
              refine ⟨53025249365313268472524021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70700332487084357963365361 53025249365313268472524021)
              ·
                refine ⟨4971117127998118919299127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53025249365313268472524021 4971117127998118919299127)
                ·
                  refine ⟨7456675691997178378948691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4971117127998118919299127 7456675691997178378948691)
                  ·
                    refine ⟨11185013537995767568423037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7456675691997178378948691 11185013537995767568423037)
                    ·
                      refine ⟨4194380076748412838158639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11185013537995767568423037 4194380076748412838158639)
                      ·
                        rfl

theorem cell23_8168526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3].length) (baseStart_8168526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8168526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8168526 prefixEnd_8168526 := by exact prefixLift 8168526
  have htrace : WordTrace (prefixWord ++ tailWord_8168526) baseStart_8168526 baseEnd_8168526 := by
    simpa [prefixWord, tailWord_8168526, baseEnd_8168526] using wordTrace_append hprefix tailTrace_8168526
  have hstable : (prefixWord ++ tailWord_8168526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8168526).length < 2 ^ (prefixWord ++ tailWord_8168526).sum := by decide
  have hdescent : baseEnd_8168526 < baseStart_8168526 := by decide
  rcases family_descends (prefixWord ++ tailWord_8168526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8168545 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 3, 1, 6]
def baseStart_8168545 : Nat := 118140960795 + 8168545 * 2 ^ 59
def prefixEnd_8168545 : Nat := 4983230072969 + 3 ^ 40 * 8168545 * 2
def baseEnd_8168545 : Nat := 4194389832880848263821051

theorem tailTrace_8168545 : CollatzResearch.WordTrace tailWord_8168545 prefixEnd_8168545 4194389832880848263821051 := by
  unfold tailWord_8168545
  simp only [CollatzResearch.WordTrace]
  refine ⟨297931312191764016263403089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198620874794509344175602059 297931312191764016263403089)
  ·
    refine ⟨223448484143823012197552317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297931312191764016263403089 223448484143823012197552317)
    ·
      refine ⟨83793181553933629574082119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223448484143823012197552317 83793181553933629574082119)
      ·
        refine ⟨125689772330900444361123179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83793181553933629574082119 125689772330900444361123179)
        ·
          refine ⟨188534658496350666541684769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125689772330900444361123179 188534658496350666541684769)
          ·
            refine ⟨141400993872262999906263577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188534658496350666541684769 141400993872262999906263577)
            ·
              refine ⟨106050745404197249929697683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141400993872262999906263577 106050745404197249929697683)
              ·
                refine ⟨159076118106295874894546525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106050745404197249929697683 159076118106295874894546525)
                ·
                  refine ⟨59653544289860953085454947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159076118106295874894546525 59653544289860953085454947)
                  ·
                    refine ⟨89480316434791429628182421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59653544289860953085454947 89480316434791429628182421)
                    ·
                      refine ⟨4194389832880848263821051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89480316434791429628182421 4194389832880848263821051)
                      ·
                        rfl

theorem cell23_8168545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_8168545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8168545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8168545 prefixEnd_8168545 := by exact prefixLift 8168545
  have htrace : WordTrace (prefixWord ++ tailWord_8168545) baseStart_8168545 baseEnd_8168545 := by
    simpa [prefixWord, tailWord_8168545, baseEnd_8168545] using wordTrace_append hprefix tailTrace_8168545
  have hstable : (prefixWord ++ tailWord_8168545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8168545).length < 2 ^ (prefixWord ++ tailWord_8168545).sum := by decide
  have hdescent : baseEnd_8168545 < baseStart_8168545 := by decide
  rcases family_descends (prefixWord ++ tailWord_8168545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8168572 : List Nat := [2, 2, 2, 1, 1, 3, 5, 7]
def baseStart_8168572 : Nat := 118140960795 + 8168572 * 2 ^ 59
def prefixEnd_8168572 : Nat := 4983230072969 + 3 ^ 40 * 8168572 * 2
def baseEnd_8168572 : Nat := 155348285068834061414201

theorem tailTrace_8168572 : CollatzResearch.WordTrace tailWord_8168572 prefixEnd_8168572 155348285068834061414201 := by
  unfold tailWord_8168572
  simp only [CollatzResearch.WordTrace]
  refine ⟨148966148481333099937317985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198621531308444133249757313 148966148481333099937317985)
  ·
    refine ⟨111724611360999824952988489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148966148481333099937317985 111724611360999824952988489)
    ·
      refine ⟨83793458520749868714741367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111724611360999824952988489 83793458520749868714741367)
      ·
        refine ⟨125690187781124803072112051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83793458520749868714741367 125690187781124803072112051)
        ·
          refine ⟨188535281671687204608168077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125690187781124803072112051 188535281671687204608168077)
          ·
            refine ⟨70700730626882701728063029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188535281671687204608168077 70700730626882701728063029)
            ·
              refine ⟨6628193496270253287005909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70700730626882701728063029 6628193496270253287005909)
              ·
                refine ⟨155348285068834061414201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6628193496270253287005909 155348285068834061414201)
                ·
                  rfl

theorem cell23_8168572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 7].length) (baseStart_8168572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8168572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8168572 prefixEnd_8168572 := by exact prefixLift 8168572
  have htrace : WordTrace (prefixWord ++ tailWord_8168572) baseStart_8168572 baseEnd_8168572 := by
    simpa [prefixWord, tailWord_8168572, baseEnd_8168572] using wordTrace_append hprefix tailTrace_8168572
  have hstable : (prefixWord ++ tailWord_8168572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8168572).length < 2 ^ (prefixWord ++ tailWord_8168572).sum := by decide
  have hdescent : baseEnd_8168572 < baseStart_8168572 := by decide
  rcases family_descends (prefixWord ++ tailWord_8168572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8168626 : List Nat := [3, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2]
def baseStart_8168626 : Nat := 118140960795 + 8168626 * 2 ^ 59
def prefixEnd_8168626 : Nat := 4983230072969 + 3 ^ 40 * 8168626 * 2
def baseEnd_8168626 : Nat := 4194431424813862446908179

theorem tailTrace_8168626 : CollatzResearch.WordTrace tailWord_8168626 prefixEnd_8168626 4194431424813862446908179 := by
  unfold tailWord_8168626
  simp only [CollatzResearch.WordTrace]
  refine ⟨74483566626117641774275433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198622844336313711398067821 74483566626117641774275433)
  ·
    refine ⟨55862674969588231330706575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74483566626117641774275433 55862674969588231330706575)
    ·
      refine ⟨83794012454382346996059863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55862674969588231330706575 83794012454382346996059863)
      ·
        refine ⟨125691018681573520494089795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83794012454382346996059863 125691018681573520494089795)
        ·
          refine ⟨188536528022360280741134693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125691018681573520494089795 188536528022360280741134693)
          ·
            refine ⟨35350599004192552638962755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188536528022360280741134693 35350599004192552638962755)
            ·
              refine ⟨53025898506288828958444133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35350599004192552638962755 53025898506288828958444133)
              ·
                refine ⟨9942355969929155429708275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53025898506288828958444133 9942355969929155429708275)
                ·
                  refine ⟨14913533954893733144562413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9942355969929155429708275 14913533954893733144562413)
                  ·
                    refine ⟨5592575233085149929210905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14913533954893733144562413 5592575233085149929210905)
                    ·
                      refine ⟨4194431424813862446908179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5592575233085149929210905 4194431424813862446908179)
                      ·
                        rfl

theorem cell23_8168626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2].length) (baseStart_8168626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8168626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8168626 prefixEnd_8168626 := by exact prefixLift 8168626
  have htrace : WordTrace (prefixWord ++ tailWord_8168626) baseStart_8168626 baseEnd_8168626 := by
    simpa [prefixWord, tailWord_8168626, baseEnd_8168626] using wordTrace_append hprefix tailTrace_8168626
  have hstable : (prefixWord ++ tailWord_8168626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8168626).length < 2 ^ (prefixWord ++ tailWord_8168626).sum := by decide
  have hdescent : baseEnd_8168626 < baseStart_8168626 := by decide
  rcases family_descends (prefixWord ++ tailWord_8168626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8168639 : List Nat := [1, 1, 2, 2, 2, 2, 2, 4, 1, 4, 2]
def baseStart_8168639 : Nat := 118140960795 + 8168639 * 2 ^ 59
def prefixEnd_8168639 : Nat := 4983230072969 + 3 ^ 40 * 8168639 * 2
def baseEnd_8168639 : Nat := 4194438100062370896045619

theorem tailTrace_8168639 : CollatzResearch.WordTrace tailWord_8168639 prefixEnd_8168639 4194438100062370896045619 := by
  unfold tailWord_8168639
  simp only [CollatzResearch.WordTrace]
  refine ⟨297934740653423470317324971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198623160435615646878216647 297934740653423470317324971)
  ·
    refine ⟨446902110980135205475987457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297934740653423470317324971 446902110980135205475987457)
    ·
      refine ⟨335176583235101404106990593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446902110980135205475987457 335176583235101404106990593)
      ·
        refine ⟨251382437426326053080242945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335176583235101404106990593 251382437426326053080242945)
        ·
          refine ⟨188536828069744539810182209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251382437426326053080242945 188536828069744539810182209)
          ·
            refine ⟨141402621052308404857636657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188536828069744539810182209 141402621052308404857636657)
            ·
              refine ⟨106051965789231303643227493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141402621052308404857636657 106051965789231303643227493)
              ·
                refine ⟨19884743585480869433105155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106051965789231303643227493 19884743585480869433105155)
                ·
                  refine ⟨29827115378221304149657733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19884743585480869433105155 29827115378221304149657733)
                  ·
                    refine ⟨5592584133416494528060825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29827115378221304149657733 5592584133416494528060825)
                    ·
                      refine ⟨4194438100062370896045619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5592584133416494528060825 4194438100062370896045619)
                      ·
                        rfl

theorem cell23_8168639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 4, 2].length) (baseStart_8168639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8168639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8168639 prefixEnd_8168639 := by exact prefixLift 8168639
  have htrace : WordTrace (prefixWord ++ tailWord_8168639) baseStart_8168639 baseEnd_8168639 := by
    simpa [prefixWord, tailWord_8168639, baseEnd_8168639] using wordTrace_append hprefix tailTrace_8168639
  have hstable : (prefixWord ++ tailWord_8168639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8168639).length < 2 ^ (prefixWord ++ tailWord_8168639).sum := by decide
  have hdescent : baseEnd_8168639 < baseStart_8168639 := by decide
  rcases family_descends (prefixWord ++ tailWord_8168639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8168673 : List Nat := [1, 2, 3, 1, 3, 3, 1, 3, 2, 2, 2]
def baseStart_8168673 : Nat := 118140960795 + 8168673 * 2 ^ 59
def prefixEnd_8168673 : Nat := 4983230072969 + 3 ^ 40 * 8168673 * 2
def baseEnd_8168673 : Nat := 4194455558404623763020463

theorem tailTrace_8168673 : CollatzResearch.WordTrace tailWord_8168673 prefixEnd_8168673 4194455558404623763020463 := by
  unfold tailWord_8168673
  simp only [CollatzResearch.WordTrace]
  refine ⟨297935980735300294124062673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198623987156866862749375115 297935980735300294124062673)
  ·
    refine ⟨223451985551475220593047005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297935980735300294124062673 223451985551475220593047005)
    ·
      refine ⟨83794494581803207722392627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223451985551475220593047005 83794494581803207722392627)
      ·
        refine ⟨125691741872704811583588941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83794494581803207722392627 125691741872704811583588941)
        ·
          refine ⟨47134403202264304343845853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125691741872704811583588941 47134403202264304343845853)
          ·
            refine ⟨17675401200849114128942195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47134403202264304343845853 17675401200849114128942195)
            ·
              refine ⟨26513101801273671193413293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17675401200849114128942195 26513101801273671193413293)
              ·
                refine ⟨9942413175477626697529985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26513101801273671193413293 9942413175477626697529985)
                ·
                  refine ⟨7456809881608220023147489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9942413175477626697529985 7456809881608220023147489)
                  ·
                    refine ⟨5592607411206165017360617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7456809881608220023147489 5592607411206165017360617)
                    ·
                      refine ⟨4194455558404623763020463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5592607411206165017360617 4194455558404623763020463)
                      ·
                        rfl

theorem cell23_8168673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3, 2, 2, 2].length) (baseStart_8168673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8168673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8168673 prefixEnd_8168673 := by exact prefixLift 8168673
  have htrace : WordTrace (prefixWord ++ tailWord_8168673) baseStart_8168673 baseEnd_8168673 := by
    simpa [prefixWord, tailWord_8168673, baseEnd_8168673] using wordTrace_append hprefix tailTrace_8168673
  have hstable : (prefixWord ++ tailWord_8168673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8168673).length < 2 ^ (prefixWord ++ tailWord_8168673).sum := by decide
  have hdescent : baseEnd_8168673 < baseStart_8168673 := by decide
  rcases family_descends (prefixWord ++ tailWord_8168673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8168739 : List Nat := [1, 1, 1, 4, 2, 3, 1, 1, 5, 4]
def baseStart_8168739 : Nat := 118140960795 + 8168739 * 2 ^ 59
def prefixEnd_8168739 : Nat := 4983230072969 + 3 ^ 40 * 8168739 * 2
def baseEnd_8168739 : Nat := 1398163149375940168265053

theorem tailTrace_8168739 : CollatzResearch.WordTrace tailWord_8168739 prefixEnd_8168739 1398163149375940168265053 := by
  unfold tailWord_8168739
  simp only [CollatzResearch.WordTrace]
  refine ⟨297938387953061187395965271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198625591968707458263976847 297938387953061187395965271)
  ·
    refine ⟨446907581929591781093947907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297938387953061187395965271 446907581929591781093947907)
    ·
      refine ⟨670361372894387671640921861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446907581929591781093947907 670361372894387671640921861)
      ·
        refine ⟨125692757417697688432672849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 670361372894387671640921861 125692757417697688432672849)
        ·
          refine ⟨94269568063273266324504637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125692757417697688432672849 94269568063273266324504637)
          ·
            refine ⟨35351088023727474871689239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94269568063273266324504637 35351088023727474871689239)
            ·
              refine ⟨53026632035591212307533859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35351088023727474871689239 53026632035591212307533859)
              ·
                refine ⟨79539948053386818461300789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53026632035591212307533859 79539948053386818461300789)
                ·
                  refine ⟨7456870130005014230746949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79539948053386818461300789 7456870130005014230746949)
                  ·
                    refine ⟨1398163149375940168265053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7456870130005014230746949 1398163149375940168265053)
                    ·
                      rfl

theorem cell23_8168739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 5, 4].length) (baseStart_8168739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8168739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8168739 prefixEnd_8168739 := by exact prefixLift 8168739
  have htrace : WordTrace (prefixWord ++ tailWord_8168739) baseStart_8168739 baseEnd_8168739 := by
    simpa [prefixWord, tailWord_8168739, baseEnd_8168739] using wordTrace_append hprefix tailTrace_8168739
  have hstable : (prefixWord ++ tailWord_8168739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8168739).length < 2 ^ (prefixWord ++ tailWord_8168739).sum := by decide
  have hdescent : baseEnd_8168739 < baseStart_8168739 := by decide
  rcases family_descends (prefixWord ++ tailWord_8168739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8168746 : List Nat := [3, 1, 4, 2, 1, 2, 1, 1, 1, 3, 4]
def baseStart_8168746 : Nat := 118140960795 + 8168746 * 2 ^ 59
def prefixEnd_8168746 : Nat := 4983230072969 + 3 ^ 40 * 8168746 * 2
def baseEnd_8168746 : Nat := 4194493042492401977407627

theorem tailTrace_8168746 : CollatzResearch.WordTrace tailWord_8168746 prefixEnd_8168746 4194493042492401977407627 := by
  unfold tailWord_8168746
  simp only [CollatzResearch.WordTrace]
  refine ⟨74484660816008956897867523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198625762176023885060980061 74484660816008956897867523)
  ·
    refine ⟨111726991224013435346801285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74484660816008956897867523 111726991224013435346801285)
    ·
      refine ⟨20948810854502519127525241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111726991224013435346801285 20948810854502519127525241)
      ·
        refine ⟨15711608140876889345643931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20948810854502519127525241 15711608140876889345643931)
        ·
          refine ⟨23567412211315334018465897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15711608140876889345643931 23567412211315334018465897)
          ·
            refine ⟨17675559158486500513849423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23567412211315334018465897 17675559158486500513849423)
            ·
              refine ⟨26513338737729750770774135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17675559158486500513849423 26513338737729750770774135)
              ·
                refine ⟨39770008106594626156161203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26513338737729750770774135 39770008106594626156161203)
                ·
                  refine ⟨59655012159891939234241805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39770008106594626156161203 59655012159891939234241805)
                  ·
                    refine ⟨22370629559959477212840677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59655012159891939234241805 22370629559959477212840677)
                    ·
                      refine ⟨4194493042492401977407627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22370629559959477212840677 4194493042492401977407627)
                      ·
                        rfl

theorem cell23_8168746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_8168746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8168746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8168746 prefixEnd_8168746 := by exact prefixLift 8168746
  have htrace : WordTrace (prefixWord ++ tailWord_8168746) baseStart_8168746 baseEnd_8168746 := by
    simpa [prefixWord, tailWord_8168746, baseEnd_8168746] using wordTrace_append hprefix tailTrace_8168746
  have hstable : (prefixWord ++ tailWord_8168746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8168746).length < 2 ^ (prefixWord ++ tailWord_8168746).sum := by decide
  have hdescent : baseEnd_8168746 < baseStart_8168746 := by decide
  rcases family_descends (prefixWord ++ tailWord_8168746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8168752 : List Nat := [2, 1, 1, 1, 2, 2, 4, 2, 8]
def baseStart_8168752 : Nat := 118140960795 + 8168752 * 2 ^ 59
def prefixEnd_8168752 : Nat := 4983230072969 + 3 ^ 40 * 8168752 * 2
def baseEnd_8168752 : Nat := 466055124819592105992511

theorem tailTrace_8168752 : CollatzResearch.WordTrace tailWord_8168752 prefixEnd_8168752 466055124819592105992511 := by
  unfold tailWord_8168752
  simp only [CollatzResearch.WordTrace]
  refine ⟨148969431051007045308094255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198625908068009393744125673 148969431051007045308094255)
  ·
    refine ⟨223454146576510567962141383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148969431051007045308094255 223454146576510567962141383)
    ·
      refine ⟨335181219864765851943212075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223454146576510567962141383 335181219864765851943212075)
      ·
        refine ⟨502771829797148777914818113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335181219864765851943212075 502771829797148777914818113)
        ·
          refine ⟨377078872347861583436113585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 502771829797148777914818113 377078872347861583436113585)
          ·
            refine ⟨282809154260896187577085189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377078872347861583436113585 282809154260896187577085189)
            ·
              refine ⟨53026716423918035170703473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 282809154260896187577085189 53026716423918035170703473)
              ·
                refine ⟨39770037317938526378027605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53026716423918035170703473 39770037317938526378027605)
                ·
                  refine ⟨466055124819592105992511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39770037317938526378027605 466055124819592105992511)
                  ·
                    rfl

theorem cell23_8168752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 8].length) (baseStart_8168752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8168752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8168752 prefixEnd_8168752 := by exact prefixLift 8168752
  have htrace : WordTrace (prefixWord ++ tailWord_8168752) baseStart_8168752 baseEnd_8168752 := by
    simpa [prefixWord, tailWord_8168752, baseEnd_8168752] using wordTrace_append hprefix tailTrace_8168752
  have hstable : (prefixWord ++ tailWord_8168752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8168752).length < 2 ^ (prefixWord ++ tailWord_8168752).sum := by decide
  have hdescent : baseEnd_8168752 < baseStart_8168752 := by decide
  rcases family_descends (prefixWord ++ tailWord_8168752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8168756 : List Nat := [2, 5, 1, 1, 1, 1, 1, 2, 5, 4]
def baseStart_8168756 : Nat := 118140960795 + 8168756 * 2 ^ 59
def prefixEnd_8168756 : Nat := 4983230072969 + 3 ^ 40 * 8168756 * 2
def baseEnd_8168756 : Nat := 1398166059099648979427527

theorem tailTrace_8168756 : CollatzResearch.WordTrace tailWord_8168756 prefixEnd_8168756 1398166059099648979427527 := by
  unfold tailWord_8168756
  simp only [CollatzResearch.WordTrace]
  refine ⟨148969503996999799649667061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198626005329333066199556081 148969503996999799649667061)
  ·
    refine ⟨13965890999718731217156287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148969503996999799649667061 13965890999718731217156287)
    ·
      refine ⟨20948836499578096825734431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13965890999718731217156287 20948836499578096825734431)
      ·
        refine ⟨31423254749367145238601647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20948836499578096825734431 31423254749367145238601647)
        ·
          refine ⟨47134882124050717857902471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31423254749367145238601647 47134882124050717857902471)
          ·
            refine ⟨70702323186076076786853707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47134882124050717857902471 70702323186076076786853707)
            ·
              refine ⟨106053484779114115180280561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70702323186076076786853707 106053484779114115180280561)
              ·
                refine ⟨79540113584335586385210421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106053484779114115180280561 79540113584335586385210421)
                ·
                  refine ⟨7456885648531461223613477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79540113584335586385210421 7456885648531461223613477)
                  ·
                    refine ⟨1398166059099648979427527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7456885648531461223613477 1398166059099648979427527)
                    ·
                      rfl

theorem cell23_8168756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_8168756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8168756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8168756 prefixEnd_8168756 := by exact prefixLift 8168756
  have htrace : WordTrace (prefixWord ++ tailWord_8168756) baseStart_8168756 baseEnd_8168756 := by
    simpa [prefixWord, tailWord_8168756, baseEnd_8168756] using wordTrace_append hprefix tailTrace_8168756
  have hstable : (prefixWord ++ tailWord_8168756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8168756).length < 2 ^ (prefixWord ++ tailWord_8168756).sum := by decide
  have hdescent : baseEnd_8168756 < baseStart_8168756 := by decide
  rcases family_descends (prefixWord ++ tailWord_8168756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8168766 : List Nat := [4, 2, 1, 2, 1, 1, 2, 1, 4, 2, 3]
def baseStart_8168766 : Nat := 118140960795 + 8168766 * 2 ^ 59
def prefixEnd_8168766 : Nat := 4983230072969 + 3 ^ 40 * 8168766 * 2
def baseEnd_8168766 : Nat := 4194503312105491899157535

theorem tailTrace_8168766 : CollatzResearch.WordTrace tailWord_8168766 prefixEnd_8168766 4194503312105491899157535 := by
  unfold tailWord_8168766
  simp only [CollatzResearch.WordTrace]
  refine ⟨37242421590495421375899769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198626248482642247338132101 37242421590495421375899769)
  ·
    refine ⟨27931816192871566031924827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37242421590495421375899769 27931816192871566031924827)
    ·
      refine ⟨41897724289307349047887241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27931816192871566031924827 41897724289307349047887241)
      ·
        refine ⟨31423293216980511785915431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41897724289307349047887241 31423293216980511785915431)
        ·
          refine ⟨47134939825470767678873147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31423293216980511785915431 47134939825470767678873147)
          ·
            refine ⟨70702409738206151518309721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47134939825470767678873147 70702409738206151518309721)
            ·
              refine ⟨53026807303654613638732291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70702409738206151518309721 53026807303654613638732291)
              ·
                refine ⟨79540210955481920458098437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53026807303654613638732291 79540210955481920458098437)
                ·
                  refine ⟨14913789554152860085893457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79540210955481920458098437 14913789554152860085893457)
                  ·
                    refine ⟨11185342165614645064420093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14913789554152860085893457 11185342165614645064420093)
                    ·
                      refine ⟨4194503312105491899157535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11185342165614645064420093 4194503312105491899157535)
                      ·
                        rfl

theorem cell23_8168766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_8168766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8168766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8168766 prefixEnd_8168766 := by exact prefixLift 8168766
  have htrace : WordTrace (prefixWord ++ tailWord_8168766) baseStart_8168766 baseEnd_8168766 := by
    simpa [prefixWord, tailWord_8168766, baseEnd_8168766] using wordTrace_append hprefix tailTrace_8168766
  have hstable : (prefixWord ++ tailWord_8168766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8168766).length < 2 ^ (prefixWord ++ tailWord_8168766).sum := by decide
  have hdescent : baseEnd_8168766 < baseStart_8168766 := by decide
  rcases family_descends (prefixWord ++ tailWord_8168766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8168807 : List Nat := [1, 1, 5, 1, 5, 1, 1, 3, 1, 4]
def baseStart_8168807 : Nat := 118140960795 + 8168807 * 2 ^ 59
def prefixEnd_8168807 : Nat := 4983230072969 + 3 ^ 40 * 8168807 * 2
def baseEnd_8168807 : Nat := 1398174788270775412914949

theorem tailTrace_8168807 : CollatzResearch.WordTrace tailWord_8168807 prefixEnd_8168807 1398174788270775412914949 := by
  unfold tailWord_8168807
  simp only [CollatzResearch.WordTrace]
  refine ⟨297940868116814835009440675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198627245411209890006293783 297940868116814835009440675)
  ·
    refine ⟨446911302175222252514161013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297940868116814835009440675 446911302175222252514161013)
    ·
      refine ⟨41897934578927086173202595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 446911302175222252514161013 41897934578927086173202595)
      ·
        refine ⟨62846901868390629259803893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41897934578927086173202595 62846901868390629259803893)
        ·
          refine ⟨5891897050161621493106615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62846901868390629259803893 5891897050161621493106615)
          ·
            refine ⟨8837845575242432239659923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5891897050161621493106615 8837845575242432239659923)
            ·
              refine ⟨13256768362863648359489885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8837845575242432239659923 13256768362863648359489885)
              ·
                refine ⟨4971288136073868134808707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13256768362863648359489885 4971288136073868134808707)
                ·
                  refine ⟨7456932204110802202213061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4971288136073868134808707 7456932204110802202213061)
                  ·
                    refine ⟨1398174788270775412914949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7456932204110802202213061 1398174788270775412914949)
                    ·
                      rfl

theorem cell23_8168807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_8168807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8168807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8168807 prefixEnd_8168807 := by exact prefixLift 8168807
  have htrace : WordTrace (prefixWord ++ tailWord_8168807) baseStart_8168807 baseEnd_8168807 := by
    simpa [prefixWord, tailWord_8168807, baseEnd_8168807] using wordTrace_append hprefix tailTrace_8168807
  have hstable : (prefixWord ++ tailWord_8168807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8168807).length < 2 ^ (prefixWord ++ tailWord_8168807).sum := by decide
  have hdescent : baseEnd_8168807 < baseStart_8168807 := by decide
  rcases family_descends (prefixWord ++ tailWord_8168807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8168853 : List Nat := [1, 3, 2, 1, 1, 2, 2, 4, 3, 2, 2]
def baseStart_8168853 : Nat := 118140960795 + 8168853 * 2 ^ 59
def prefixEnd_8168853 : Nat := 4983230072969 + 3 ^ 40 * 8168853 * 2
def baseEnd_8168853 : Nat := 4194547984922433058769635

theorem tailTrace_8168853 : CollatzResearch.WordTrace tailWord_8168853 prefixEnd_8168853 4194547984922433058769635 := by
  unfold tailWord_8168853
  simp only [CollatzResearch.WordTrace]
  refine ⟨297942545874648184865615213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198628363916432123243743475 297942545874648184865615213)
  ·
    refine ⟨111728454702993069324605705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297942545874648184865615213 111728454702993069324605705)
    ·
      refine ⟨83796341027244801993454279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111728454702993069324605705 83796341027244801993454279)
      ·
        refine ⟨125694511540867202990181419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83796341027244801993454279 125694511540867202990181419)
        ·
          refine ⟨188541767311300804485272129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125694511540867202990181419 188541767311300804485272129)
          ·
            refine ⟨141406325483475603363954097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188541767311300804485272129 141406325483475603363954097)
            ·
              refine ⟨106054744112606702522965573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141406325483475603363954097 106054744112606702522965573)
              ·
                refine ⟨19885264521113756723056045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106054744112606702522965573 19885264521113756723056045)
                ·
                  refine ⟨7456974195417658771146017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19885264521113756723056045 7456974195417658771146017)
                  ·
                    refine ⟨5592730646563244078359513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7456974195417658771146017 5592730646563244078359513)
                    ·
                      refine ⟨4194547984922433058769635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5592730646563244078359513 4194547984922433058769635)
                      ·
                        rfl

theorem cell23_8168853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 3, 2, 2].length) (baseStart_8168853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8168853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8168853 prefixEnd_8168853 := by exact prefixLift 8168853
  have htrace : WordTrace (prefixWord ++ tailWord_8168853) baseStart_8168853 baseEnd_8168853 := by
    simpa [prefixWord, tailWord_8168853, baseEnd_8168853] using wordTrace_append hprefix tailTrace_8168853
  have hstable : (prefixWord ++ tailWord_8168853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8168853).length < 2 ^ (prefixWord ++ tailWord_8168853).sum := by decide
  have hdescent : baseEnd_8168853 < baseStart_8168853 := by decide
  rcases family_descends (prefixWord ++ tailWord_8168853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8168866 : List Nat := [3, 3, 1, 2, 1, 2, 1, 1, 3, 2, 4]
def baseStart_8168866 : Nat := 118140960795 + 8168866 * 2 ^ 59
def prefixEnd_8168866 : Nat := 4983230072969 + 3 ^ 40 * 8168866 * 2
def baseEnd_8168866 : Nat := 4194554660170941507907075

theorem tailTrace_8168866 : CollatzResearch.WordTrace tailWord_8168866 prefixEnd_8168866 4194554660170941507907075 := by
  unfold tailWord_8168866
  simp only [CollatzResearch.WordTrace]
  refine ⟨74485755005900272021459613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198628680015734058723892301 74485755005900272021459613)
  ·
    refine ⟨27932158127212602008047355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74485755005900272021459613 27932158127212602008047355)
    ·
      refine ⟨41898237190818903012071033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27932158127212602008047355 41898237190818903012071033)
      ·
        refine ⟨31423677893114177259053275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41898237190818903012071033 31423677893114177259053275)
        ·
          refine ⟨47135516839671265888579913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31423677893114177259053275 47135516839671265888579913)
          ·
            refine ⟨35351637629753449416434935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47135516839671265888579913 35351637629753449416434935)
            ·
              refine ⟨53027456444630174124652403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35351637629753449416434935 53027456444630174124652403)
              ·
                refine ⟨79541184666945261186978605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53027456444630174124652403 79541184666945261186978605)
                ·
                  refine ⟨29827944250104472945116977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79541184666945261186978605 29827944250104472945116977)
                  ·
                    refine ⟨22370958187578354708837733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29827944250104472945116977 22370958187578354708837733)
                    ·
                      refine ⟨4194554660170941507907075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22370958187578354708837733 4194554660170941507907075)
                      ·
                        rfl

theorem cell23_8168866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_8168866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8168866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8168866 prefixEnd_8168866 := by exact prefixLift 8168866
  have htrace : WordTrace (prefixWord ++ tailWord_8168866) baseStart_8168866 baseEnd_8168866 := by
    simpa [prefixWord, tailWord_8168866, baseEnd_8168866] using wordTrace_append hprefix tailTrace_8168866
  have hstable : (prefixWord ++ tailWord_8168866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8168866).length < 2 ^ (prefixWord ++ tailWord_8168866).sum := by decide
  have hdescent : baseEnd_8168866 < baseStart_8168866 := by decide
  rcases family_descends (prefixWord ++ tailWord_8168866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8168903 : List Nat := [1, 1, 4, 1, 1, 3, 1, 5, 2, 1, 3]
def baseStart_8168903 : Nat := 118140960795 + 8168903 * 2 ^ 59
def prefixEnd_8168903 : Nat := 4983230072969 + 3 ^ 40 * 8168903 * 2
def baseEnd_8168903 : Nat := 4194573658955157863144405

theorem tailTrace_8168903 : CollatzResearch.WordTrace tailWord_8168903 prefixEnd_8168903 4194573658955157863144405 := by
  unfold tailWord_8168903
  simp only [CollatzResearch.WordTrace]
  refine ⟨297944369524467043404935363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198629579682978028936623575 297944369524467043404935363)
  ·
    refine ⟨446916554286700565107403045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297944369524467043404935363 446916554286700565107403045)
    ·
      refine ⟨83796853928756355957638071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 446916554286700565107403045 83796853928756355957638071)
      ·
        refine ⟨125695280893134533936457107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83796853928756355957638071 125695280893134533936457107)
        ·
          refine ⟨188542921339701800904685661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125695280893134533936457107 188542921339701800904685661)
          ·
            refine ⟨70703595502388175339257123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188542921339701800904685661 70703595502388175339257123)
            ·
              refine ⟨106055393253582263008885685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70703595502388175339257123 106055393253582263008885685)
              ·
                refine ⟨9942693117523337157083033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106055393253582263008885685 9942693117523337157083033)
                ·
                  refine ⟨7457019838142502867812275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9942693117523337157083033 7457019838142502867812275)
                  ·
                    refine ⟨11185529757213754301718413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7457019838142502867812275 11185529757213754301718413)
                    ·
                      refine ⟨4194573658955157863144405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11185529757213754301718413 4194573658955157863144405)
                      ·
                        rfl

theorem cell23_8168903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5, 2, 1, 3].length) (baseStart_8168903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8168903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8168903 prefixEnd_8168903 := by exact prefixLift 8168903
  have htrace : WordTrace (prefixWord ++ tailWord_8168903) baseStart_8168903 baseEnd_8168903 := by
    simpa [prefixWord, tailWord_8168903, baseEnd_8168903] using wordTrace_append hprefix tailTrace_8168903
  have hstable : (prefixWord ++ tailWord_8168903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8168903).length < 2 ^ (prefixWord ++ tailWord_8168903).sum := by decide
  have hdescent : baseEnd_8168903 < baseStart_8168903 := by decide
  rcases family_descends (prefixWord ++ tailWord_8168903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8168956 : List Nat := [2, 2, 2, 1, 2, 1, 4, 1, 2, 2, 4]
def baseStart_8168956 : Nat := 118140960795 + 8168956 * 2 ^ 59
def prefixEnd_8168956 : Nat := 4983230072969 + 3 ^ 40 * 8168956 * 2
def baseEnd_8168956 : Nat := 4194600873429846155781661

theorem tailTrace_8168956 : CollatzResearch.WordTrace tailWord_8168956 prefixEnd_8168956 4194600873429846155781661 := by
  unfold tailWord_8168956
  simp only [CollatzResearch.WordTrace]
  refine ⟨148973151296637516728307361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198630868395516688971076481 148973151296637516728307361)
  ·
    refine ⟨111729863472478137546230521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148973151296637516728307361 111729863472478137546230521)
    ·
      refine ⟨83797397604358603159672891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111729863472478137546230521 83797397604358603159672891)
      ·
        refine ⟨125696096406537904739509337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83797397604358603159672891 125696096406537904739509337)
        ·
          refine ⟨94272072304903428554632003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125696096406537904739509337 94272072304903428554632003)
          ·
            refine ⟨141408108457355142831948005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94272072304903428554632003 141408108457355142831948005)
            ·
              refine ⟨26514020335754089280990251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141408108457355142831948005 26514020335754089280990251)
              ·
                refine ⟨39771030503631133921485377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26514020335754089280990251 39771030503631133921485377)
                ·
                  refine ⟨29828272877723350441114033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39771030503631133921485377 29828272877723350441114033)
                  ·
                    refine ⟨22371204658292512830835525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29828272877723350441114033 22371204658292512830835525)
                    ·
                      refine ⟨4194600873429846155781661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22371204658292512830835525 4194600873429846155781661)
                      ·
                        rfl

theorem cell23_8168956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_8168956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8168956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8168956 prefixEnd_8168956 := by exact prefixLift 8168956
  have htrace : WordTrace (prefixWord ++ tailWord_8168956) baseStart_8168956 baseEnd_8168956 := by
    simpa [prefixWord, tailWord_8168956, baseEnd_8168956] using wordTrace_append hprefix tailTrace_8168956
  have hstable : (prefixWord ++ tailWord_8168956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8168956).length < 2 ^ (prefixWord ++ tailWord_8168956).sum := by decide
  have hdescent : baseEnd_8168956 < baseStart_8168956 := by decide
  rcases family_descends (prefixWord ++ tailWord_8168956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8168980 : List Nat := [2, 4, 3, 1, 2, 1, 1, 1, 2, 1, 5]
def baseStart_8168980 : Nat := 118140960795 + 8168980 * 2 ^ 59
def prefixEnd_8168980 : Nat := 4983230072969 + 3 ^ 40 * 8168980 * 2
def baseEnd_8168980 : Nat := 4194613196965554061881551

theorem tailTrace_8168980 : CollatzResearch.WordTrace tailWord_8168980 prefixEnd_8168980 4194613196965554061881551 := by
  unfold tailWord_8168980
  simp only [CollatzResearch.WordTrace]
  refine ⟨148973588972594042777744197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198631451963458723703658929 148973588972594042777744197)
  ·
    refine ⟨27932547932361383020827037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148973588972594042777744197 27932547932361383020827037)
    ·
      refine ⟨10474705474635518632810139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27932547932361383020827037 10474705474635518632810139)
      ·
        refine ⟨15712058211953277949215209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10474705474635518632810139 15712058211953277949215209)
        ·
          refine ⟨11784043658964958461911407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15712058211953277949215209 11784043658964958461911407)
          ·
            refine ⟨17676065488447437692867111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11784043658964958461911407 17676065488447437692867111)
            ·
              refine ⟨26514098232671156539300667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17676065488447437692867111 26514098232671156539300667)
              ·
                refine ⟨39771147349006734808951001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26514098232671156539300667 39771147349006734808951001)
                ·
                  refine ⟨29828360511755051106713251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39771147349006734808951001 29828360511755051106713251)
                  ·
                    refine ⟨44742540767632576660069877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29828360511755051106713251 44742540767632576660069877)
                    ·
                      refine ⟨4194613196965554061881551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44742540767632576660069877 4194613196965554061881551)
                      ·
                        rfl

theorem cell23_8168980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_8168980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8168980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8168980 prefixEnd_8168980 := by exact prefixLift 8168980
  have htrace : WordTrace (prefixWord ++ tailWord_8168980) baseStart_8168980 baseEnd_8168980 := by
    simpa [prefixWord, tailWord_8168980, baseEnd_8168980] using wordTrace_append hprefix tailTrace_8168980
  have hstable : (prefixWord ++ tailWord_8168980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8168980).length < 2 ^ (prefixWord ++ tailWord_8168980).sum := by decide
  have hdescent : baseEnd_8168980 < baseStart_8168980 := by decide
  rcases family_descends (prefixWord ++ tailWord_8168980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169000 : List Nat := [2, 1, 5, 2, 2, 2, 1, 1, 7]
def baseStart_8169000 : Nat := 118140960795 + 8169000 * 2 ^ 59
def prefixEnd_8169000 : Nat := 4983230072969 + 3 ^ 40 * 8169000 * 2
def baseEnd_8169000 : Nat := 466069274064293775959051

theorem tailTrace_8169000 : CollatzResearch.WordTrace tailWord_8169000 prefixEnd_8169000 466069274064293775959051 := by
  unfold tailWord_8169000
  simp only [CollatzResearch.WordTrace]
  refine ⟨148973953702557814485608227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198631938270077085980810969 148973953702557814485608227)
  ·
    refine ⟨223460930553836721728412341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148973953702557814485608227 223460930553836721728412341)
    ·
      refine ⟨20949462239422192662038657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 223460930553836721728412341 20949462239422192662038657)
      ·
        refine ⟨15712096679566644496528993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20949462239422192662038657 15712096679566644496528993)
        ·
          refine ⟨11784072509674983372396745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15712096679566644496528993 11784072509674983372396745)
          ·
            refine ⟨8838054382256237529297559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11784072509674983372396745 8838054382256237529297559)
            ·
              refine ⟨13257081573384356293946339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8838054382256237529297559 13257081573384356293946339)
              ·
                refine ⟨19885622360076534440919509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13257081573384356293946339 19885622360076534440919509)
                ·
                  refine ⟨466069274064293775959051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19885622360076534440919509 466069274064293775959051)
                  ·
                    rfl

theorem cell23_8169000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 7].length) (baseStart_8169000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169000 prefixEnd_8169000 := by exact prefixLift 8169000
  have htrace : WordTrace (prefixWord ++ tailWord_8169000) baseStart_8169000 baseEnd_8169000 := by
    simpa [prefixWord, tailWord_8169000, baseEnd_8169000] using wordTrace_append hprefix tailTrace_8169000
  have hstable : (prefixWord ++ tailWord_8169000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169000).length < 2 ^ (prefixWord ++ tailWord_8169000).sum := by decide
  have hdescent : baseEnd_8169000 < baseStart_8169000 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169150 : List Nat := [4, 2, 1, 1, 2, 2, 1, 2, 4, 4]
def baseStart_8169150 : Nat := 118140960795 + 8169150 * 2 ^ 59
def prefixEnd_8169150 : Nat := 4983230072969 + 3 ^ 40 * 8169150 * 2
def baseEnd_8169150 : Nat := 1398233496225606132251923

theorem tailTrace_8169150 : CollatzResearch.WordTrace tailWord_8169150 prefixEnd_8169150 1398233496225606132251923 := by
  unfold tailWord_8169150
  simp only [CollatzResearch.WordTrace]
  refine ⟨37244172294321525573647113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198635585569714803059451269 37244172294321525573647113)
  ·
    refine ⟨27933129220741144180235335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37244172294321525573647113 27933129220741144180235335)
    ·
      refine ⟨41899693831111716270353003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27933129220741144180235335 41899693831111716270353003)
      ·
        refine ⟨62849540746667574405529505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41899693831111716270353003 62849540746667574405529505)
        ·
          refine ⟨47137155560000680804147129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62849540746667574405529505 47137155560000680804147129)
          ·
            refine ⟨35352866670000510603110347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47137155560000680804147129 35352866670000510603110347)
            ·
              refine ⟨53029300005000765904665521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35352866670000510603110347 53029300005000765904665521)
              ·
                refine ⟨39771975003750574428499141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53029300005000765904665521 39771975003750574428499141)
                ·
                  refine ⟨7457245313203232705343589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39771975003750574428499141 7457245313203232705343589)
                  ·
                    refine ⟨1398233496225606132251923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7457245313203232705343589 1398233496225606132251923)
                    ·
                      rfl

theorem cell23_8169150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_8169150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169150 prefixEnd_8169150 := by exact prefixLift 8169150
  have htrace : WordTrace (prefixWord ++ tailWord_8169150) baseStart_8169150 baseEnd_8169150 := by
    simpa [prefixWord, tailWord_8169150, baseEnd_8169150] using wordTrace_append hprefix tailTrace_8169150
  have hstable : (prefixWord ++ tailWord_8169150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169150).length < 2 ^ (prefixWord ++ tailWord_8169150).sum := by decide
  have hdescent : baseEnd_8169150 < baseStart_8169150 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169160 : List Nat := [2, 1, 3, 1, 2, 2, 1, 5, 1, 2, 3]
def baseStart_8169160 : Nat := 118140960795 + 8169160 * 2 ^ 59
def prefixEnd_8169160 : Nat := 4983230072969 + 3 ^ 40 * 8169160 * 2
def baseEnd_8169160 : Nat := 4194705623483363357630723

theorem tailTrace_8169160 : CollatzResearch.WordTrace tailWord_8169160 prefixEnd_8169160 4194705623483363357630723 := by
  unfold tailWord_8169160
  simp only [CollatzResearch.WordTrace]
  refine ⟨148976871542267988148520467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198635828723023984198027289 148976871542267988148520467)
  ·
    refine ⟨223465307313401982222780701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148976871542267988148520467 223465307313401982222780701)
    ·
      refine ⟨83799490242525743333542763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223465307313401982222780701 83799490242525743333542763)
      ·
        refine ⟨125699235363788615000314145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83799490242525743333542763 125699235363788615000314145)
        ·
          refine ⟨94274426522841461250235609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125699235363788615000314145 94274426522841461250235609)
          ·
            refine ⟨70705819892131095937676707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94274426522841461250235609 70705819892131095937676707)
            ·
              refine ⟨106058729838196643906515061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70705819892131095937676707 106058729838196643906515061)
              ·
                refine ⟨9943005922330935366235787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106058729838196643906515061 9943005922330935366235787)
                ·
                  refine ⟨14914508883496403049353681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9943005922330935366235787 14914508883496403049353681)
                  ·
                    refine ⟨11185881662622302287015261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14914508883496403049353681 11185881662622302287015261)
                    ·
                      refine ⟨4194705623483363357630723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11185881662622302287015261 4194705623483363357630723)
                      ·
                        rfl

theorem cell23_8169160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5, 1, 2, 3].length) (baseStart_8169160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169160 prefixEnd_8169160 := by exact prefixLift 8169160
  have htrace : WordTrace (prefixWord ++ tailWord_8169160) baseStart_8169160 baseEnd_8169160 := by
    simpa [prefixWord, tailWord_8169160, baseEnd_8169160] using wordTrace_append hprefix tailTrace_8169160
  have hstable : (prefixWord ++ tailWord_8169160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169160).length < 2 ^ (prefixWord ++ tailWord_8169160).sum := by decide
  have hdescent : baseEnd_8169160 < baseStart_8169160 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169191 : List Nat := [1, 1, 5, 4, 2, 1, 1, 2, 1, 1, 4]
def baseStart_8169191 : Nat := 118140960795 + 8169191 * 2 ^ 59
def prefixEnd_8169191 : Nat := 4983230072969 + 3 ^ 40 * 8169191 * 2
def baseEnd_8169191 : Nat := 4194721541383652736343081

theorem tailTrace_8169191 : CollatzResearch.WordTrace tailWord_8169191 prefixEnd_8169191 4194721541383652736343081 := by
  unfold tailWord_8169191
  simp only [CollatzResearch.WordTrace]
  refine ⟨297954873747423668591419427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198636582498282445727612951 297954873747423668591419427)
  ·
    refine ⟨446932310621135502887129141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297954873747423668591419427 446932310621135502887129141)
    ·
      refine ⟨41899904120731453395668357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 446932310621135502887129141 41899904120731453395668357)
      ·
        refine ⟨7856232022637147511687817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41899904120731453395668357 7856232022637147511687817)
        ·
          refine ⟨5892174016977860633765863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7856232022637147511687817 5892174016977860633765863)
          ·
            refine ⟨8838261025466790950648795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5892174016977860633765863 8838261025466790950648795)
            ·
              refine ⟨13257391538200186425973193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8838261025466790950648795 13257391538200186425973193)
              ·
                refine ⟨9943043653650139819479895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13257391538200186425973193 9943043653650139819479895)
                ·
                  refine ⟨14914565480475209729219843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9943043653650139819479895 14914565480475209729219843)
                  ·
                    refine ⟨22371848220712814593829765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14914565480475209729219843 22371848220712814593829765)
                    ·
                      refine ⟨4194721541383652736343081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22371848220712814593829765 4194721541383652736343081)
                      ·
                        rfl

theorem cell23_8169191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_8169191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169191 prefixEnd_8169191 := by exact prefixLift 8169191
  have htrace : WordTrace (prefixWord ++ tailWord_8169191) baseStart_8169191 baseEnd_8169191 := by
    simpa [prefixWord, tailWord_8169191, baseEnd_8169191] using wordTrace_append hprefix tailTrace_8169191
  have hstable : (prefixWord ++ tailWord_8169191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169191).length < 2 ^ (prefixWord ++ tailWord_8169191).sum := by decide
  have hdescent : baseEnd_8169191 < baseStart_8169191 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169204 : List Nat := [2, 6, 1, 1, 1, 2, 1, 2, 1, 2, 4]
def baseStart_8169204 : Nat := 118140960795 + 8169204 * 2 ^ 59
def prefixEnd_8169204 : Nat := 4983230072969 + 3 ^ 40 * 8169204 * 2
def baseEnd_8169204 : Nat := 4194728216632161185480521

theorem tailTrace_8169204 : CollatzResearch.WordTrace tailWord_8169204 prefixEnd_8169204 4194728216632161185480521 := by
  unfold tailWord_8169204
  simp only [CollatzResearch.WordTrace]
  refine ⟨148977673948188285905821333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198636898597584381207761777 148977673948188285905821333)
  ·
    refine ⟨6983328466321325901835375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 148977673948188285905821333 6983328466321325901835375)
    ·
      refine ⟨10474992699481988852753063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6983328466321325901835375 10474992699481988852753063)
      ·
        refine ⟨15712489049222983279129595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10474992699481988852753063 15712489049222983279129595)
        ·
          refine ⟨23568733573834474918694393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15712489049222983279129595 23568733573834474918694393)
          ·
            refine ⟨17676550180375856189020795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23568733573834474918694393 17676550180375856189020795)
            ·
              refine ⟨26514825270563784283531193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17676550180375856189020795 26514825270563784283531193)
              ·
                refine ⟨19886118952922838212648395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26514825270563784283531193 19886118952922838212648395)
                ·
                  refine ⟨29829178429384257318972593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19886118952922838212648395 29829178429384257318972593)
                  ·
                    refine ⟨22371883822038192989229445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29829178429384257318972593 22371883822038192989229445)
                    ·
                      refine ⟨4194728216632161185480521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22371883822038192989229445 4194728216632161185480521)
                      ·
                        rfl

theorem cell23_8169204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_8169204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169204 prefixEnd_8169204 := by exact prefixLift 8169204
  have htrace : WordTrace (prefixWord ++ tailWord_8169204) baseStart_8169204 baseEnd_8169204 := by
    simpa [prefixWord, tailWord_8169204, baseEnd_8169204] using wordTrace_append hprefix tailTrace_8169204
  have hstable : (prefixWord ++ tailWord_8169204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169204).length < 2 ^ (prefixWord ++ tailWord_8169204).sum := by decide
  have hdescent : baseEnd_8169204 < baseStart_8169204 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169217 : List Nat := [1, 2, 4, 1, 1, 1, 2, 5, 1, 3, 2]
def baseStart_8169217 : Nat := 118140960795 + 8169217 * 2 ^ 59
def prefixEnd_8169217 : Nat := 4983230072969 + 3 ^ 40 * 8169217 * 2
def baseEnd_8169217 : Nat := 4194734891880669634617961

theorem tailTrace_8169217 : CollatzResearch.WordTrace tailWord_8169217 prefixEnd_8169217 4194734891880669634617961 := by
  unfold tailWord_8169217
  simp only [CollatzResearch.WordTrace]
  refine ⟨297955822045329475031865905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198637214696886316687910603 297955822045329475031865905)
  ·
    refine ⟨223466866533997106273899429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297955822045329475031865905 223466866533997106273899429)
    ·
      refine ⟨41900037475124457426356143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223466866533997106273899429 41900037475124457426356143)
      ·
        refine ⟨62850056212686686139534215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41900037475124457426356143 62850056212686686139534215)
        ·
          refine ⟨94275084319030029209301323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62850056212686686139534215 94275084319030029209301323)
          ·
            refine ⟨141412626478545043813951985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94275084319030029209301323 141412626478545043813951985)
            ·
              refine ⟨106059469858908782860463989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141412626478545043813951985 106059469858908782860463989)
              ·
                refine ⟨9943075299272698393168499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106059469858908782860463989 9943075299272698393168499)
                ·
                  refine ⟨14914612948909047589752749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9943075299272698393168499 14914612948909047589752749)
                  ·
                    refine ⟨5592979855840892846157281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14914612948909047589752749 5592979855840892846157281)
                    ·
                      refine ⟨4194734891880669634617961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5592979855840892846157281 4194734891880669634617961)
                      ·
                        rfl

theorem cell23_8169217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5, 1, 3, 2].length) (baseStart_8169217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169217 prefixEnd_8169217 := by exact prefixLift 8169217
  have htrace : WordTrace (prefixWord ++ tailWord_8169217) baseStart_8169217 baseEnd_8169217 := by
    simpa [prefixWord, tailWord_8169217, baseEnd_8169217] using wordTrace_append hprefix tailTrace_8169217
  have hstable : (prefixWord ++ tailWord_8169217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169217).length < 2 ^ (prefixWord ++ tailWord_8169217).sum := by decide
  have hdescent : baseEnd_8169217 < baseStart_8169217 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169234 : List Nat := [3, 2, 4, 1, 1, 1, 1, 2, 3, 3, 2]
def baseStart_8169234 : Nat := 118140960795 + 8169234 * 2 ^ 59
def prefixEnd_8169234 : Nat := 4983230072969 + 3 ^ 40 * 8169234 * 2
def baseEnd_8169234 : Nat := 4194743621051796068105383

theorem tailTrace_8169234 : CollatzResearch.WordTrace tailWord_8169234 prefixEnd_8169234 4194743621051796068105383 := by
  unfold tailWord_8169234
  simp only [CollatzResearch.WordTrace]
  refine ⟨74489110521566971733808689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198637628057511924623489837 74489110521566971733808689)
  ·
    refine ⟨55866832891175228800356517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74489110521566971733808689 55866832891175228800356517)
    ·
      refine ⟨10475031167095355400066847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55866832891175228800356517 10475031167095355400066847)
      ·
        refine ⟨15712546750643033100100271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10475031167095355400066847 15712546750643033100100271)
        ·
          refine ⟨23568820125964549650150407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15712546750643033100100271 23568820125964549650150407)
          ·
            refine ⟨35353230188946824475225611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23568820125964549650150407 35353230188946824475225611)
            ·
              refine ⟨53029845283420236712838417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35353230188946824475225611 53029845283420236712838417)
              ·
                refine ⟨39772383962565177534628813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53029845283420236712838417 39772383962565177534628813)
                ·
                  refine ⟨14914643985961941575485805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39772383962565177534628813 14914643985961941575485805)
                  ·
                    refine ⟨5592991494735728090807177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14914643985961941575485805 5592991494735728090807177)
                    ·
                      refine ⟨4194743621051796068105383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5592991494735728090807177 4194743621051796068105383)
                      ·
                        rfl

theorem cell23_8169234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_8169234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169234 prefixEnd_8169234 := by exact prefixLift 8169234
  have htrace : WordTrace (prefixWord ++ tailWord_8169234) baseStart_8169234 baseEnd_8169234 := by
    simpa [prefixWord, tailWord_8169234, baseEnd_8169234] using wordTrace_append hprefix tailTrace_8169234
  have hstable : (prefixWord ++ tailWord_8169234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169234).length < 2 ^ (prefixWord ++ tailWord_8169234).sum := by decide
  have hdescent : baseEnd_8169234 < baseStart_8169234 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169243 : List Nat := [1, 1, 1, 1, 1, 1, 4, 5, 2, 2, 4]
def baseStart_8169243 : Nat := 118140960795 + 8169243 * 2 ^ 59
def prefixEnd_8169243 : Nat := 4983230072969 + 3 ^ 40 * 8169243 * 2
def baseEnd_8169243 : Nat := 4194748242377686532892841

theorem tailTrace_8169243 : CollatzResearch.WordTrace tailWord_8169243 prefixEnd_8169243 4194748242377686532892841 := by
  unfold tailWord_8169243
  simp only [CollatzResearch.WordTrace]
  refine ⟨297956770343235281472312383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198637846895490187648208255 297956770343235281472312383)
  ·
    refine ⟨446935155514852922208468575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297956770343235281472312383 446935155514852922208468575)
    ·
      refine ⟨670402733272279383312702863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446935155514852922208468575 670402733272279383312702863)
      ·
        refine ⟨1005604099908419074969054295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 670402733272279383312702863 1005604099908419074969054295)
        ·
          refine ⟨1508406149862628612453581443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1005604099908419074969054295 1508406149862628612453581443)
          ·
            refine ⟨2262609224793942918680372165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1508406149862628612453581443 2262609224793942918680372165)
            ·
              refine ⟨424239229648864297252569781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2262609224793942918680372165 424239229648864297252569781)
              ·
                refine ⟨39772427779581027867428417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 424239229648864297252569781 39772427779581027867428417)
                ·
                  refine ⟨29829320834685770900571313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39772427779581027867428417 29829320834685770900571313)
                  ·
                    refine ⟨22371990626014328175428485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29829320834685770900571313 22371990626014328175428485)
                    ·
                      refine ⟨4194748242377686532892841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22371990626014328175428485 4194748242377686532892841)
                      ·
                        rfl

theorem cell23_8169243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2, 4].length) (baseStart_8169243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169243 prefixEnd_8169243 := by exact prefixLift 8169243
  have htrace : WordTrace (prefixWord ++ tailWord_8169243) baseStart_8169243 baseEnd_8169243 := by
    simpa [prefixWord, tailWord_8169243, baseEnd_8169243] using wordTrace_append hprefix tailTrace_8169243
  have hstable : (prefixWord ++ tailWord_8169243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169243).length < 2 ^ (prefixWord ++ tailWord_8169243).sum := by decide
  have hdescent : baseEnd_8169243 < baseStart_8169243 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169247 : List Nat := [1, 1, 2, 4, 2, 1, 4, 1, 1, 4, 2]
def baseStart_8169247 : Nat := 118140960795 + 8169247 * 2 ^ 59
def prefixEnd_8169247 : Nat := 4983230072969 + 3 ^ 40 * 8169247 * 2
def baseEnd_8169247 : Nat := 4194750296300304517242823

theorem tailTrace_8169247 : CollatzResearch.WordTrace tailWord_8169247 prefixEnd_8169247 4194750296300304517242823 := by
  unfold tailWord_8169247
  simp only [CollatzResearch.WordTrace]
  refine ⟨297956916235220790155457995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198637944156813860103638663 297956916235220790155457995)
  ·
    refine ⟨446935374352831185233186993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297956916235220790155457995 446935374352831185233186993)
    ·
      refine ⟨335201530764623388924890245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446935374352831185233186993 335201530764623388924890245)
      ·
        refine ⟨62850287018366885423416921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 335201530764623388924890245 62850287018366885423416921)
        ·
          refine ⟨47137715263775164067562691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62850287018366885423416921 47137715263775164067562691)
          ·
            refine ⟨70706572895662746101344037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47137715263775164067562691 70706572895662746101344037)
            ·
              refine ⟨13257482417936764894002007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70706572895662746101344037 13257482417936764894002007)
              ·
                refine ⟨19886223626905147341003011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13257482417936764894002007 19886223626905147341003011)
                ·
                  refine ⟨29829335440357721011504517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19886223626905147341003011 29829335440357721011504517)
                  ·
                    refine ⟨5593000395067072689657097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29829335440357721011504517 5593000395067072689657097)
                    ·
                      refine ⟨4194750296300304517242823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5593000395067072689657097 4194750296300304517242823)
                      ·
                        rfl

theorem cell23_8169247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 4, 2].length) (baseStart_8169247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169247 prefixEnd_8169247 := by exact prefixLift 8169247
  have htrace : WordTrace (prefixWord ++ tailWord_8169247) baseStart_8169247 baseEnd_8169247 := by
    simpa [prefixWord, tailWord_8169247, baseEnd_8169247] using wordTrace_append hprefix tailTrace_8169247
  have hstable : (prefixWord ++ tailWord_8169247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169247).length < 2 ^ (prefixWord ++ tailWord_8169247).sum := by decide
  have hdescent : baseEnd_8169247 < baseStart_8169247 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169250 : List Nat := [3, 3, 1, 1, 2, 1, 1, 2, 2, 4, 3]
def baseStart_8169250 : Nat := 118140960795 + 8169250 * 2 ^ 59
def prefixEnd_8169250 : Nat := 4983230072969 + 3 ^ 40 * 8169250 * 2
def baseEnd_8169250 : Nat := 4194751836742268005505309

theorem tailTrace_8169250 : CollatzResearch.WordTrace tailWord_8169250 prefixEnd_8169250 4194751836742268005505309 := by
  unfold tailWord_8169250
  simp only [CollatzResearch.WordTrace]
  refine ⟨74489256413552480416954301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198638017102806614445211469 74489256413552480416954301)
  ·
    refine ⟨27933471155082180156357863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74489256413552480416954301 27933471155082180156357863)
    ·
      refine ⟨41900206732623270234536795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27933471155082180156357863 41900206732623270234536795)
      ·
        refine ⟨62850310098934905351805193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41900206732623270234536795 62850310098934905351805193)
        ·
          refine ⟨47137732574201179013853895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62850310098934905351805193 47137732574201179013853895)
          ·
            refine ⟨70706598861301768520780843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47137732574201179013853895 70706598861301768520780843)
            ·
              refine ⟨106059898291952652781171265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70706598861301768520780843 106059898291952652781171265)
              ·
                refine ⟨79544923718964489585878449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106059898291952652781171265 79544923718964489585878449)
                ·
                  refine ⟨59658692789223367189408837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79544923718964489585878449 59658692789223367189408837)
                  ·
                    refine ⟨11186004897979381348014157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59658692789223367189408837 11186004897979381348014157)
                    ·
                      refine ⟨4194751836742268005505309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11186004897979381348014157 4194751836742268005505309)
                      ·
                        rfl

theorem cell23_8169250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_8169250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169250 prefixEnd_8169250 := by exact prefixLift 8169250
  have htrace : WordTrace (prefixWord ++ tailWord_8169250) baseStart_8169250 baseEnd_8169250 := by
    simpa [prefixWord, tailWord_8169250, baseEnd_8169250] using wordTrace_append hprefix tailTrace_8169250
  have hstable : (prefixWord ++ tailWord_8169250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169250).length < 2 ^ (prefixWord ++ tailWord_8169250).sum := by decide
  have hdescent : baseEnd_8169250 < baseStart_8169250 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169253 : List Nat := [1, 3, 1, 2, 3, 2, 1, 1, 9]
def baseStart_8169253 : Nat := 118140960795 + 8169253 * 2 ^ 59
def prefixEnd_8169253 : Nat := 4983230072969 + 3 ^ 40 * 8169253 * 2
def baseEnd_8169253 : Nat := 466083708576025721529755

theorem tailTrace_8169253 : CollatzResearch.WordTrace tailWord_8169253 prefixEnd_8169253 466083708576025721529755 := by
  unfold tailWord_8169253
  simp only [CollatzResearch.WordTrace]
  refine ⟨297957135073199053180176413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198638090048799368786784275 297957135073199053180176413)
  ·
    refine ⟨111733925652449644942566155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297957135073199053180176413 111733925652449644942566155)
    ·
      refine ⟨167600888478674467413849233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111733925652449644942566155 167600888478674467413849233)
      ·
        refine ⟨125700666359005850560386925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167600888478674467413849233 125700666359005850560386925)
        ·
          refine ⟨47137749884627193960145097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125700666359005850560386925 47137749884627193960145097)
          ·
            refine ⟨35353312413470395470108823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47137749884627193960145097 35353312413470395470108823)
            ·
              refine ⟨53029968620205593205163235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35353312413470395470108823 53029968620205593205163235)
              ·
                refine ⟨79544952930308389807744853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53029968620205593205163235 79544952930308389807744853)
                ·
                  refine ⟨466083708576025721529755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 79544952930308389807744853 466083708576025721529755)
                  ·
                    rfl

theorem cell23_8169253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 9].length) (baseStart_8169253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169253 prefixEnd_8169253 := by exact prefixLift 8169253
  have htrace : WordTrace (prefixWord ++ tailWord_8169253) baseStart_8169253 baseEnd_8169253 := by
    simpa [prefixWord, tailWord_8169253, baseEnd_8169253] using wordTrace_append hprefix tailTrace_8169253
  have hstable : (prefixWord ++ tailWord_8169253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169253).length < 2 ^ (prefixWord ++ tailWord_8169253).sum := by decide
  have hdescent : baseEnd_8169253 < baseStart_8169253 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169268 : List Nat := [2, 5, 1, 1, 2, 3, 2, 1, 1, 3, 2]
def baseStart_8169268 : Nat := 118140960795 + 8169268 * 2 ^ 59
def prefixEnd_8169268 : Nat := 4983230072969 + 3 ^ 40 * 8169268 * 2
def baseEnd_8169268 : Nat := 4194761079394048935080227

theorem tailTrace_8169268 : CollatzResearch.WordTrace tailWord_8169268 prefixEnd_8169268 4194761079394048935080227 := by
  unfold tailWord_8169268
  simp only [CollatzResearch.WordTrace]
  refine ⟨148978841084072355370986229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198638454778763140494648305 148978841084072355370986229)
  ·
    refine ⟨13966766351631783316029959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148978841084072355370986229 13966766351631783316029959)
    ·
      refine ⟨20950149527447674974044939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13966766351631783316029959 20950149527447674974044939)
      ·
        refine ⟨31425224291171512461067409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20950149527447674974044939 31425224291171512461067409)
        ·
          refine ⟨23568918218378634345800557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31425224291171512461067409 23568918218378634345800557)
          ·
            refine ⟨8838344331891987879675209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23568918218378634345800557 8838344331891987879675209)
            ·
              refine ⟨6628758248918990909756407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8838344331891987879675209 6628758248918990909756407)
              ·
                refine ⟨9943137373378486364634611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6628758248918990909756407 9943137373378486364634611)
                ·
                  refine ⟨14914706060067729546951917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9943137373378486364634611 14914706060067729546951917)
                  ·
                    refine ⟨5593014772525398580106969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14914706060067729546951917 5593014772525398580106969)
                    ·
                      refine ⟨4194761079394048935080227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5593014772525398580106969 4194761079394048935080227)
                      ·
                        rfl

theorem cell23_8169268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_8169268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169268 prefixEnd_8169268 := by exact prefixLift 8169268
  have htrace : WordTrace (prefixWord ++ tailWord_8169268) baseStart_8169268 baseEnd_8169268 := by
    simpa [prefixWord, tailWord_8169268, baseEnd_8169268] using wordTrace_append hprefix tailTrace_8169268
  have hstable : (prefixWord ++ tailWord_8169268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169268).length < 2 ^ (prefixWord ++ tailWord_8169268).sum := by decide
  have hdescent : baseEnd_8169268 < baseStart_8169268 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169300 : List Nat := [2, 4, 1, 1, 3, 1, 1, 2, 1, 7]
def baseStart_8169300 : Nat := 118140960795 + 8169300 * 2 ^ 59
def prefixEnd_8169300 : Nat := 4983230072969 + 3 ^ 40 * 8169300 * 2
def baseEnd_8169300 : Nat := 1398259170258330936626693

theorem tailTrace_8169300 : CollatzResearch.WordTrace tailWord_8169300 prefixEnd_8169300 1398259170258330936626693 := by
  unfold tailWord_8169300
  simp only [CollatzResearch.WordTrace]
  refine ⟨148979424652014390103568677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198639232869352520138091569 148979424652014390103568677)
  ·
    refine ⟨27933642122252698144419127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148979424652014390103568677 27933642122252698144419127)
    ·
      refine ⟨41900463183379047216628691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27933642122252698144419127 41900463183379047216628691)
      ·
        refine ⟨62850694775068570824943037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41900463183379047216628691 62850694775068570824943037)
        ·
          refine ⟨23569010540650714059353639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62850694775068570824943037 23569010540650714059353639)
          ·
            refine ⟨35353515810976071089030459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23569010540650714059353639 35353515810976071089030459)
            ·
              refine ⟨53030273716464106633545689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35353515810976071089030459 53030273716464106633545689)
              ·
                refine ⟨39772705287348079975159267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53030273716464106633545689 39772705287348079975159267)
                ·
                  refine ⟨59659057931022119962738901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39772705287348079975159267 59659057931022119962738901)
                  ·
                    refine ⟨1398259170258330936626693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59659057931022119962738901 1398259170258330936626693)
                    ·
                      rfl

theorem cell23_8169300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_8169300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169300 prefixEnd_8169300 := by exact prefixLift 8169300
  have htrace : WordTrace (prefixWord ++ tailWord_8169300) baseStart_8169300 baseEnd_8169300 := by
    simpa [prefixWord, tailWord_8169300, baseEnd_8169300] using wordTrace_append hprefix tailTrace_8169300
  have hstable : (prefixWord ++ tailWord_8169300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169300).length < 2 ^ (prefixWord ++ tailWord_8169300).sum := by decide
  have hdescent : baseEnd_8169300 < baseStart_8169300 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169313 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 2, 8]
def baseStart_8169313 : Nat := 118140960795 + 8169313 * 2 ^ 59
def prefixEnd_8169313 : Nat := 4983230072969 + 3 ^ 40 * 8169313 * 2
def baseEnd_8169313 : Nat := 1398261395341167086339173

theorem tailTrace_8169313 : CollatzResearch.WordTrace tailWord_8169313 prefixEnd_8169313 1398261395341167086339173 := by
  unfold tailWord_8169313
  simp only [CollatzResearch.WordTrace]
  refine ⟨297959323452981683427360593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198639548968654455618240395 297959323452981683427360593)
  ·
    refine ⟨223469492589736262570520445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297959323452981683427360593 223469492589736262570520445)
    ·
      refine ⟨83801059721151098463945167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223469492589736262570520445 83801059721151098463945167)
      ·
        refine ⟨125701589581726647695917751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83801059721151098463945167 125701589581726647695917751)
        ·
          refine ⟨188552384372589971543876627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125701589581726647695917751 188552384372589971543876627)
          ·
            refine ⟨282828576558884957315814941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188552384372589971543876627 282828576558884957315814941)
            ·
              refine ⟨106060716209581858993430603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 282828576558884957315814941 106060716209581858993430603)
              ·
                refine ⟨159091074314372788490145905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106060716209581858993430603 159091074314372788490145905)
                ·
                  refine ⟨119318305735779591367609429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159091074314372788490145905 119318305735779591367609429)
                  ·
                    refine ⟨1398261395341167086339173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119318305735779591367609429 1398261395341167086339173)
                    ·
                      rfl

theorem cell23_8169313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_8169313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169313 prefixEnd_8169313 := by exact prefixLift 8169313
  have htrace : WordTrace (prefixWord ++ tailWord_8169313) baseStart_8169313 baseEnd_8169313 := by
    simpa [prefixWord, tailWord_8169313, baseEnd_8169313] using wordTrace_append hprefix tailTrace_8169313
  have hstable : (prefixWord ++ tailWord_8169313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169313).length < 2 ^ (prefixWord ++ tailWord_8169313).sum := by decide
  have hdescent : baseEnd_8169313 < baseStart_8169313 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169320 : List Nat := [2, 1, 4, 2, 1, 1, 1, 3, 1, 3, 4]
def baseStart_8169320 : Nat := 118140960795 + 8169320 * 2 ^ 59
def prefixEnd_8169320 : Nat := 4983230072969 + 3 ^ 40 * 8169320 * 2
def baseEnd_8169320 : Nat := 4194787780388082731629987

theorem tailTrace_8169320 : CollatzResearch.WordTrace tailWord_8169320 prefixEnd_8169320 4194787780388082731629987 := by
  unfold tailWord_8169320
  simp only [CollatzResearch.WordTrace]
  refine ⟨148979789381978161811432707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198639719175970882415243609 148979789381978161811432707)
  ·
    refine ⟨223469684072967242717149061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148979789381978161811432707 223469684072967242717149061)
    ·
      refine ⟨41900565763681358009465449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223469684072967242717149061 41900565763681358009465449)
      ·
        refine ⟨31425424322761018507099087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41900565763681358009465449 31425424322761018507099087)
        ·
          refine ⟨47138136484141527760648631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31425424322761018507099087 47138136484141527760648631)
          ·
            refine ⟨70707204726212291640972947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47138136484141527760648631 70707204726212291640972947)
            ·
              refine ⟨106060807089318437461459421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70707204726212291640972947 106060807089318437461459421)
              ·
                refine ⟨39772802658494414048047283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106060807089318437461459421 39772802658494414048047283)
                ·
                  refine ⟨59659203987741621072070925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39772802658494414048047283 59659203987741621072070925)
                  ·
                    refine ⟨22372201495403107902026597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59659203987741621072070925 22372201495403107902026597)
                    ·
                      refine ⟨4194787780388082731629987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22372201495403107902026597 4194787780388082731629987)
                      ·
                        rfl

theorem cell23_8169320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_8169320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169320 prefixEnd_8169320 := by exact prefixLift 8169320
  have htrace : WordTrace (prefixWord ++ tailWord_8169320) baseStart_8169320 baseEnd_8169320 := by
    simpa [prefixWord, tailWord_8169320, baseEnd_8169320] using wordTrace_append hprefix tailTrace_8169320
  have hstable : (prefixWord ++ tailWord_8169320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169320).length < 2 ^ (prefixWord ++ tailWord_8169320).sum := by decide
  have hdescent : baseEnd_8169320 < baseStart_8169320 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169323 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 5]
def baseStart_8169323 : Nat := 118140960795 + 8169323 * 2 ^ 59
def prefixEnd_8169323 : Nat := 4983230072969 + 3 ^ 40 * 8169323 * 2
def baseEnd_8169323 : Nat := 4194789320830046219892473

theorem tailTrace_8169323 : CollatzResearch.WordTrace tailWord_8169323 prefixEnd_8169323 4194789320830046219892473 := by
  unfold tailWord_8169323
  simp only [CollatzResearch.WordTrace]
  refine ⟨297959688182945455135224623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198639792121963636756816415 297959688182945455135224623)
  ·
    refine ⟨446939532274418182702836935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297959688182945455135224623 446939532274418182702836935)
    ·
      refine ⟨670409298411627274054255403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446939532274418182702836935 670409298411627274054255403)
      ·
        refine ⟨1005613947617440911081383105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 670409298411627274054255403 1005613947617440911081383105)
        ·
          refine ⟨754210460713080683311037329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1005613947617440911081383105 754210460713080683311037329)
          ·
            refine ⟨565657845534810512483277997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 754210460713080683311037329 565657845534810512483277997)
            ·
              refine ⟨212121692075553942181229249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 565657845534810512483277997 212121692075553942181229249)
              ·
                refine ⟨159091269056665456635921937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212121692075553942181229249 159091269056665456635921937)
                ·
                  refine ⟨119318451792499092476941453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159091269056665456635921937 119318451792499092476941453)
                  ·
                    refine ⟨44744419422187159678853045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119318451792499092476941453 44744419422187159678853045)
                    ·
                      refine ⟨4194789320830046219892473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44744419422187159678853045 4194789320830046219892473)
                      ·
                        rfl

theorem cell23_8169323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 5].length) (baseStart_8169323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169323 prefixEnd_8169323 := by exact prefixLift 8169323
  have htrace : WordTrace (prefixWord ++ tailWord_8169323) baseStart_8169323 baseEnd_8169323 := by
    simpa [prefixWord, tailWord_8169323, baseEnd_8169323] using wordTrace_append hprefix tailTrace_8169323
  have hstable : (prefixWord ++ tailWord_8169323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169323).length < 2 ^ (prefixWord ++ tailWord_8169323).sum := by decide
  have hdescent : baseEnd_8169323 < baseStart_8169323 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169334 : List Nat := [5, 1, 1, 3, 2, 1, 1, 2, 2, 5]
def baseStart_8169334 : Nat := 118140960795 + 8169334 * 2 ^ 59
def prefixEnd_8169334 : Nat := 4983230072969 + 3 ^ 40 * 8169334 * 2
def baseEnd_8169334 : Nat := 1398264989705748558951641

theorem tailTrace_8169334 : CollatzResearch.WordTrace tailWord_8169334 prefixEnd_8169334 1398264989705748558951641 := by
  unfold tailWord_8169334
  simp only [CollatzResearch.WordTrace]
  refine ⟨18622505586619100250867191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198640059590603736009250037 18622505586619100250867191)
  ·
    refine ⟨27933758379928650376300787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18622505586619100250867191 27933758379928650376300787)
    ·
      refine ⟨41900637569892975564451181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27933758379928650376300787 41900637569892975564451181)
      ·
        refine ⟨15712739088709865836669193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41900637569892975564451181 15712739088709865836669193)
        ·
          refine ⟨11784554316532399377501895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15712739088709865836669193 11784554316532399377501895)
          ·
            refine ⟨17676831474798599066252843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11784554316532399377501895 17676831474798599066252843)
            ·
              refine ⟨26515247212197898599379265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17676831474798599066252843 26515247212197898599379265)
              ·
                refine ⟨19886435409148423949534449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26515247212197898599379265 19886435409148423949534449)
                ·
                  refine ⟨14914826556861317962150837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19886435409148423949534449 14914826556861317962150837)
                  ·
                    refine ⟨1398264989705748558951641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14914826556861317962150837 1398264989705748558951641)
                    ·
                      rfl

theorem cell23_8169334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_8169334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169334 prefixEnd_8169334 := by exact prefixLift 8169334
  have htrace : WordTrace (prefixWord ++ tailWord_8169334) baseStart_8169334 baseEnd_8169334 := by
    simpa [prefixWord, tailWord_8169334, baseEnd_8169334] using wordTrace_append hprefix tailTrace_8169334
  have hstable : (prefixWord ++ tailWord_8169334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169334).length < 2 ^ (prefixWord ++ tailWord_8169334).sum := by decide
  have hdescent : baseEnd_8169334 < baseStart_8169334 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169347 : List Nat := [1, 1, 1, 3, 4, 2, 3, 1, 3, 4]
def baseStart_8169347 : Nat := 118140960795 + 8169347 * 2 ^ 59
def prefixEnd_8169347 : Nat := 4983230072969 + 3 ^ 40 * 8169347 * 2
def baseEnd_8169347 : Nat := 1398267214788584708664121

theorem tailTrace_8169347 : CollatzResearch.WordTrace tailWord_8169347 prefixEnd_8169347 1398267214788584708664121 := by
  unfold tailWord_8169347
  simp only [CollatzResearch.WordTrace]
  refine ⟨297960563534858507234098295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198640375689905671489398863 297960563534858507234098295)
  ·
    refine ⟨446940845302287760851147443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297960563534858507234098295 446940845302287760851147443)
    ·
      refine ⟨670411267953431641276721165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446940845302287760851147443 670411267953431641276721165)
      ·
        refine ⟨251404225482536865478770437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 670411267953431641276721165 251404225482536865478770437)
        ·
          refine ⟨47138292277975662277269457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 251404225482536865478770437 47138292277975662277269457)
          ·
            refine ⟨35353719208481746707952093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47138292277975662277269457 35353719208481746707952093)
            ·
              refine ⟨13257644703180655015482035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35353719208481746707952093 13257644703180655015482035)
              ·
                refine ⟨19886467054770982523223053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13257644703180655015482035 19886467054770982523223053)
                ·
                  refine ⟨7457425145539118446208645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19886467054770982523223053 7457425145539118446208645)
                  ·
                    refine ⟨1398267214788584708664121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7457425145539118446208645 1398267214788584708664121)
                    ·
                      rfl

theorem cell23_8169347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 3, 4].length) (baseStart_8169347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169347 prefixEnd_8169347 := by exact prefixLift 8169347
  have htrace : WordTrace (prefixWord ++ tailWord_8169347) baseStart_8169347 baseEnd_8169347 := by
    simpa [prefixWord, tailWord_8169347, baseEnd_8169347] using wordTrace_append hprefix tailTrace_8169347
  have hstable : (prefixWord ++ tailWord_8169347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169347).length < 2 ^ (prefixWord ++ tailWord_8169347).sum := by decide
  have hdescent : baseEnd_8169347 < baseStart_8169347 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169363 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 8]
def baseStart_8169363 : Nat := 118140960795 + 8169363 * 2 ^ 59
def prefixEnd_8169363 : Nat := 4983230072969 + 3 ^ 40 * 8169363 * 2
def baseEnd_8169363 : Nat := 4194809860056226063392289

theorem tailTrace_8169363 : CollatzResearch.WordTrace tailWord_8169363 prefixEnd_8169363 4194809860056226063392289 := by
  unfold tailWord_8169363
  simp only [CollatzResearch.WordTrace]
  refine ⟨297961147102800541966680743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198640764735200361311120495 297961147102800541966680743)
  ·
    refine ⟨446941720654200812950021115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297961147102800541966680743 446941720654200812950021115)
    ·
      refine ⟨670412580981301219425031673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446941720654200812950021115 670412580981301219425031673)
      ·
        refine ⟨502809435735975914568773755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 670412580981301219425031673 502809435735975914568773755)
        ·
          refine ⟨754214153603963871853160633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502809435735975914568773755 754214153603963871853160633)
          ·
            refine ⟨565660615202972903889870475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 754214153603963871853160633 565660615202972903889870475)
            ·
              refine ⟨848490922804459355834805713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 565660615202972903889870475 848490922804459355834805713)
              ·
                refine ⟨636368192103344516876104285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 848490922804459355834805713 636368192103344516876104285)
                ·
                  refine ⟨238638072038754193828539107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 636368192103344516876104285 238638072038754193828539107)
                  ·
                    refine ⟨357957108058131290742808661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 238638072038754193828539107 357957108058131290742808661)
                    ·
                      refine ⟨4194809860056226063392289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 357957108058131290742808661 4194809860056226063392289)
                      ·
                        rfl

theorem cell23_8169363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 8].length) (baseStart_8169363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169363 prefixEnd_8169363 := by exact prefixLift 8169363
  have htrace : WordTrace (prefixWord ++ tailWord_8169363) baseStart_8169363 baseEnd_8169363 := by
    simpa [prefixWord, tailWord_8169363, baseEnd_8169363] using wordTrace_append hprefix tailTrace_8169363
  have hstable : (prefixWord ++ tailWord_8169363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169363).length < 2 ^ (prefixWord ++ tailWord_8169363).sum := by decide
  have hdescent : baseEnd_8169363 < baseStart_8169363 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169444 : List Nat := [2, 3, 1, 1, 1, 1, 3, 2, 5, 2, 2]
def baseStart_8169444 : Nat := 118140960795 + 8169444 * 2 ^ 59
def prefixEnd_8169444 : Nat := 4983230072969 + 3 ^ 40 * 8169444 * 2
def baseEnd_8169444 : Nat := 4194851451989240246479417

theorem tailTrace_8169444 : CollatzResearch.WordTrace tailWord_8169444 prefixEnd_8169444 4194851451989240246479417 := by
  unfold tailWord_8169444
  simp only [CollatzResearch.WordTrace]
  refine ⟨148982050707753546400189693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198642734277004728533586257 148982050707753546400189693)
  ·
    refine ⟨55868269015407579900071135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148982050707753546400189693 55868269015407579900071135)
    ·
      refine ⟨83802403523111369850106703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55868269015407579900071135 83802403523111369850106703)
      ·
        refine ⟨125703605284667054775160055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83802403523111369850106703 125703605284667054775160055)
        ·
          refine ⟨188555407927000582162740083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125703605284667054775160055 188555407927000582162740083)
          ·
            refine ⟨282833111890500873244110125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188555407927000582162740083 282833111890500873244110125)
            ·
              refine ⟨106062416958937827466541297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 282833111890500873244110125 106062416958937827466541297)
              ·
                refine ⟨79546812719203370599905973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106062416958937827466541297 79546812719203370599905973)
                ·
                  refine ⟨7457513692425315993741185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79546812719203370599905973 7457513692425315993741185)
                  ·
                    refine ⟨5593135269318986995305889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7457513692425315993741185 5593135269318986995305889)
                    ·
                      refine ⟨4194851451989240246479417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5593135269318986995305889 4194851451989240246479417)
                      ·
                        rfl

theorem cell23_8169444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 5, 2, 2].length) (baseStart_8169444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169444 prefixEnd_8169444 := by exact prefixLift 8169444
  have htrace : WordTrace (prefixWord ++ tailWord_8169444) baseStart_8169444 baseEnd_8169444 := by
    simpa [prefixWord, tailWord_8169444, baseEnd_8169444] using wordTrace_append hprefix tailTrace_8169444
  have hstable : (prefixWord ++ tailWord_8169444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169444).length < 2 ^ (prefixWord ++ tailWord_8169444).sum := by decide
  have hdescent : baseEnd_8169444 < baseStart_8169444 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169450 : List Nat := [3, 1, 3, 1, 2, 1, 12]
def baseStart_8169450 : Nat := 118140960795 + 8169450 * 2 ^ 59
def prefixEnd_8169450 : Nat := 4983230072969 + 3 ^ 40 * 8169450 * 2
def baseEnd_8169450 : Nat := 51788327566335397814869

theorem tailTrace_8169450 : CollatzResearch.WordTrace tailWord_8169450 prefixEnd_8169450 51788327566335397814869 := by
  unfold tailWord_8169450
  simp only [CollatzResearch.WordTrace]
  refine ⟨74491080063371338956274451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198642880168990237216731869 74491080063371338956274451)
  ·
    refine ⟨111736620095057008434411677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74491080063371338956274451 111736620095057008434411677)
    ·
      refine ⟨41901232535646378162904379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111736620095057008434411677 41901232535646378162904379)
      ·
        refine ⟨62851848803469567244356569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41901232535646378162904379 62851848803469567244356569)
        ·
          refine ⟨47138886602602175433267427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62851848803469567244356569 47138886602602175433267427)
          ·
            refine ⟨70708329903903263149901141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47138886602602175433267427 70708329903903263149901141)
            ·
              refine ⟨51788327566335397814869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 70708329903903263149901141 51788327566335397814869)
              ·
                rfl

theorem cell23_8169450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 12].length) (baseStart_8169450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169450 prefixEnd_8169450 := by exact prefixLift 8169450
  have htrace : WordTrace (prefixWord ++ tailWord_8169450) baseStart_8169450 baseEnd_8169450 := by
    simpa [prefixWord, tailWord_8169450, baseEnd_8169450] using wordTrace_append hprefix tailTrace_8169450
  have hstable : (prefixWord ++ tailWord_8169450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169450).length < 2 ^ (prefixWord ++ tailWord_8169450).sum := by decide
  have hdescent : baseEnd_8169450 < baseStart_8169450 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169454 : List Nat := [4, 1, 2, 1, 3, 2, 1, 1, 4, 4]
def baseStart_8169454 : Nat := 118140960795 + 8169454 * 2 ^ 59
def prefixEnd_8169454 : Nat := 4983230072969 + 3 ^ 40 * 8169454 * 2
def baseEnd_8169454 : Nat := 1398285528931928402451457

theorem tailTrace_8169454 : CollatzResearch.WordTrace tailWord_8169454 prefixEnd_8169454 1398285528931928402451457 := by
  unfold tailWord_8169454
  simp only [CollatzResearch.WordTrace]
  refine ⟨37245558268183858063530427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198642977430313909672162277 37245558268183858063530427)
  ·
    refine ⟨55868337402275787095295641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37245558268183858063530427 55868337402275787095295641)
    ·
      refine ⟨41901253051706840321471731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55868337402275787095295641 41901253051706840321471731)
      ·
        refine ⟨62851879577560260482207597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41901253051706840321471731 62851879577560260482207597)
        ·
          refine ⟨23569454841585097680827849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62851879577560260482207597 23569454841585097680827849)
          ·
            refine ⟨17677091131188823260620887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23569454841585097680827849 17677091131188823260620887)
            ·
              refine ⟨26515636696783234890931331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17677091131188823260620887 26515636696783234890931331)
              ·
                refine ⟨39773455045174852336396997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26515636696783234890931331 39773455045174852336396997)
                ·
                  refine ⟨7457522820970284813074437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39773455045174852336396997 7457522820970284813074437)
                  ·
                    refine ⟨1398285528931928402451457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7457522820970284813074437 1398285528931928402451457)
                    ·
                      rfl

theorem cell23_8169454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_8169454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169454 prefixEnd_8169454 := by exact prefixLift 8169454
  have htrace : WordTrace (prefixWord ++ tailWord_8169454) baseStart_8169454 baseEnd_8169454 := by
    simpa [prefixWord, tailWord_8169454, baseEnd_8169454] using wordTrace_append hprefix tailTrace_8169454
  have hstable : (prefixWord ++ tailWord_8169454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169454).length < 2 ^ (prefixWord ++ tailWord_8169454).sum := by decide
  have hdescent : baseEnd_8169454 < baseStart_8169454 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169512 : List Nat := [2, 1, 5, 3, 2, 1, 1, 1, 3, 2, 2]
def baseStart_8169512 : Nat := 118140960795 + 8169512 * 2 ^ 59
def prefixEnd_8169512 : Nat := 4983230072969 + 3 ^ 40 * 8169512 * 2
def baseEnd_8169512 : Nat := 4194886368673745980429105

theorem tailTrace_8169512 : CollatzResearch.WordTrace tailWord_8169512 prefixEnd_8169512 4194886368673745980429105 := by
  unfold tailWord_8169512
  simp only [CollatzResearch.WordTrace]
  refine ⟨148983290789630370206927395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198644387719507160275903193 148983290789630370206927395)
  ·
    refine ⟨223474936184445555310391093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148983290789630370206927395 223474936184445555310391093)
    ·
      refine ⟨20950775267291770810349165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 223474936184445555310391093 20950775267291770810349165)
      ·
        refine ⟨7856540725234414053880937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20950775267291770810349165 7856540725234414053880937)
        ·
          refine ⟨5892405543925810540410703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7856540725234414053880937 5892405543925810540410703)
          ·
            refine ⟨8838608315888715810616055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5892405543925810540410703 8838608315888715810616055)
            ·
              refine ⟨13257912473833073715924083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8838608315888715810616055 13257912473833073715924083)
              ·
                refine ⟨19886868710749610573886125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13257912473833073715924083 19886868710749610573886125)
                ·
                  refine ⟨7457575766531103965207297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19886868710749610573886125 7457575766531103965207297)
                  ·
                    refine ⟨5593181824898327973905473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7457575766531103965207297 5593181824898327973905473)
                    ·
                      refine ⟨4194886368673745980429105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5593181824898327973905473 4194886368673745980429105)
                      ·
                        rfl

theorem cell23_8169512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_8169512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169512 prefixEnd_8169512 := by exact prefixLift 8169512
  have htrace : WordTrace (prefixWord ++ tailWord_8169512) baseStart_8169512 baseEnd_8169512 := by
    simpa [prefixWord, tailWord_8169512, baseEnd_8169512] using wordTrace_append hprefix tailTrace_8169512
  have hstable : (prefixWord ++ tailWord_8169512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169512).length < 2 ^ (prefixWord ++ tailWord_8169512).sum := by decide
  have hdescent : baseEnd_8169512 < baseStart_8169512 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169568 : List Nat := [2, 1, 1, 3, 2, 4, 2, 2, 2, 2, 2]
def baseStart_8169568 : Nat := 118140960795 + 8169568 * 2 ^ 59
def prefixEnd_8169568 : Nat := 4983230072969 + 3 ^ 40 * 8169568 * 2
def baseEnd_8169568 : Nat := 4194915123590397761328847

theorem tailTrace_8169568 : CollatzResearch.WordTrace tailWord_8169568 prefixEnd_8169568 4194915123590397761328847 := by
  unfold tailWord_8169568
  simp only [CollatzResearch.WordTrace]
  refine ⟨148984312033528930988946679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198645749378038574651928905 148984312033528930988946679)
  ·
    refine ⟨223476468050293396483420019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148984312033528930988946679 223476468050293396483420019)
    ·
      refine ⟨335214702075440094725130029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223476468050293396483420019 335214702075440094725130029)
      ·
        refine ⟨125705513278290035521923761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335214702075440094725130029 125705513278290035521923761)
        ·
          refine ⟨94279134958717526641442821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125705513278290035521923761 94279134958717526641442821)
          ·
            refine ⟨17677337804759536245270529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94279134958717526641442821 17677337804759536245270529)
            ·
              refine ⟨13258003353569652183952897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17677337804759536245270529 13258003353569652183952897)
              ·
                refine ⟨9943502515177239137964673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13258003353569652183952897 9943502515177239137964673)
                ·
                  refine ⟨7457626886382929353473505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9943502515177239137964673 7457626886382929353473505)
                  ·
                    refine ⟨5593220164787197015105129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7457626886382929353473505 5593220164787197015105129)
                    ·
                      refine ⟨4194915123590397761328847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5593220164787197015105129 4194915123590397761328847)
                      ·
                        rfl

theorem cell23_8169568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2, 2, 2, 2].length) (baseStart_8169568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169568 prefixEnd_8169568 := by exact prefixLift 8169568
  have htrace : WordTrace (prefixWord ++ tailWord_8169568) baseStart_8169568 baseEnd_8169568 := by
    simpa [prefixWord, tailWord_8169568, baseEnd_8169568] using wordTrace_append hprefix tailTrace_8169568
  have hstable : (prefixWord ++ tailWord_8169568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169568).length < 2 ^ (prefixWord ++ tailWord_8169568).sum := by decide
  have hdescent : baseEnd_8169568 < baseStart_8169568 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169584 : List Nat := [2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 3]
def baseStart_8169584 : Nat := 118140960795 + 8169584 * 2 ^ 59
def prefixEnd_8169584 : Nat := 4983230072969 + 3 ^ 40 * 8169584 * 2
def baseEnd_8169584 : Nat := 4194923339280869698728773

theorem tailTrace_8169584 : CollatzResearch.WordTrace tailWord_8169584 prefixEnd_8169584 4194923339280869698728773 := by
  unfold tailWord_8169584
  simp only [CollatzResearch.WordTrace]
  refine ⟨148984603817499948355237903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198646138423333264473650537 148984603817499948355237903)
  ·
    refine ⟨223476905726249922532856855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148984603817499948355237903 223476905726249922532856855)
    ·
      refine ⟨335215358589374883799285283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223476905726249922532856855 335215358589374883799285283)
      ·
        refine ⟨502823037884062325698927925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335215358589374883799285283 502823037884062325698927925)
        ·
          refine ⟨47139659801630843034274493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 502823037884062325698927925 47139659801630843034274493)
          ·
            refine ⟨17677372425611566137852935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47139659801630843034274493 17677372425611566137852935)
            ·
              refine ⟨26516058638417349206779403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17677372425611566137852935 26516058638417349206779403)
              ·
                refine ⟨39774087957626023810169105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26516058638417349206779403 39774087957626023810169105)
                ·
                  refine ⟨29830565968219517857626829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39774087957626023810169105 29830565968219517857626829)
                  ·
                    refine ⟨11186462238082319196610061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29830565968219517857626829 11186462238082319196610061)
                    ·
                      refine ⟨4194923339280869698728773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11186462238082319196610061 4194923339280869698728773)
                      ·
                        rfl

theorem cell23_8169584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 3].length) (baseStart_8169584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169584 prefixEnd_8169584 := by exact prefixLift 8169584
  have htrace : WordTrace (prefixWord ++ tailWord_8169584) baseStart_8169584 baseEnd_8169584 := by
    simpa [prefixWord, tailWord_8169584, baseEnd_8169584] using wordTrace_append hprefix tailTrace_8169584
  have hstable : (prefixWord ++ tailWord_8169584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169584).length < 2 ^ (prefixWord ++ tailWord_8169584).sum := by decide
  have hdescent : baseEnd_8169584 < baseStart_8169584 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169637 : List Nat := [1, 3, 1, 2, 1, 3, 1, 2, 2, 1, 6]
def baseStart_8169637 : Nat := 118140960795 + 8169637 * 2 ^ 59
def prefixEnd_8169637 : Nat := 4983230072969 + 3 ^ 40 * 8169637 * 2
def baseEnd_8169637 : Nat := 4194950553755557991366029

theorem tailTrace_8169637 : CollatzResearch.WordTrace tailWord_8169637 prefixEnd_8169637 4194950553755557991366029 := by
  unfold tailWord_8169637
  simp only [CollatzResearch.WordTrace]
  refine ⟨297971140703807886762155165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198647427135871924508103443 297971140703807886762155165)
  ·
    refine ⟨111739177763927957535808187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297971140703807886762155165 111739177763927957535808187)
    ·
      refine ⟨167608766645891936303712281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111739177763927957535808187 167608766645891936303712281)
      ·
        refine ⟨125706574984418952227784211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167608766645891936303712281 125706574984418952227784211)
        ·
          refine ⟨188559862476628428341676317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125706574984418952227784211 188559862476628428341676317)
          ·
            refine ⟨70709948428735660628128619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188559862476628428341676317 70709948428735660628128619)
            ·
              refine ⟨106064922643103490942192929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70709948428735660628128619 106064922643103490942192929)
              ·
                refine ⟨79548691982327618206644697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106064922643103490942192929 79548691982327618206644697)
                ·
                  refine ⟨59661518986745713654983523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79548691982327618206644697 59661518986745713654983523)
                  ·
                    refine ⟨89492278480118570482475285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59661518986745713654983523 89492278480118570482475285)
                    ·
                      refine ⟨4194950553755557991366029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89492278480118570482475285 4194950553755557991366029)
                      ·
                        rfl

theorem cell23_8169637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_8169637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169637 prefixEnd_8169637 := by exact prefixLift 8169637
  have htrace : WordTrace (prefixWord ++ tailWord_8169637) baseStart_8169637 baseEnd_8169637 := by
    simpa [prefixWord, tailWord_8169637, baseEnd_8169637] using wordTrace_append hprefix tailTrace_8169637
  have hstable : (prefixWord ++ tailWord_8169637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169637).length < 2 ^ (prefixWord ++ tailWord_8169637).sum := by decide
  have hdescent : baseEnd_8169637 < baseStart_8169637 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169685 : List Nat := [1, 3, 2, 4, 3, 1, 1, 1, 3, 4]
def baseStart_8169685 : Nat := 118140960795 + 8169685 * 2 ^ 59
def prefixEnd_8169685 : Nat := 4983230072969 + 3 ^ 40 * 8169685 * 2
def baseEnd_8169685 : Nat := 1398325066942324601188603

theorem tailTrace_8169685 : CollatzResearch.WordTrace tailWord_8169685 prefixEnd_8169685 1398325066942324601188603 := by
  unfold tailWord_8169685
  simp only [CollatzResearch.WordTrace]
  refine ⟨297972891407633990959902509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198648594271755993973268339 297972891407633990959902509)
  ·
    refine ⟨111739834277862746609963441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297972891407633990959902509 111739834277862746609963441)
    ·
      refine ⟨83804875708397059957472581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111739834277862746609963441 83804875708397059957472581)
      ·
        refine ⟨15713414195324448742026109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83804875708397059957472581 15713414195324448742026109)
        ·
          refine ⟨5892530323246668278259791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15713414195324448742026109 5892530323246668278259791)
          ·
            refine ⟨8838795484870002417389687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5892530323246668278259791 8838795484870002417389687)
            ·
              refine ⟨13258193227305003626084531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8838795484870002417389687 13258193227305003626084531)
              ·
                refine ⟨19887289840957505439126797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13258193227305003626084531 19887289840957505439126797)
                ·
                  refine ⟨7457733690359064539672549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19887289840957505439126797 7457733690359064539672549)
                  ·
                    refine ⟨1398325066942324601188603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7457733690359064539672549 1398325066942324601188603)
                    ·
                      rfl

theorem cell23_8169685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 3, 4].length) (baseStart_8169685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169685 prefixEnd_8169685 := by exact prefixLift 8169685
  have htrace : WordTrace (prefixWord ++ tailWord_8169685) baseStart_8169685 baseEnd_8169685 := by
    simpa [prefixWord, tailWord_8169685, baseEnd_8169685] using wordTrace_append hprefix tailTrace_8169685
  have hstable : (prefixWord ++ tailWord_8169685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169685).length < 2 ^ (prefixWord ++ tailWord_8169685).sum := by decide
  have hdescent : baseEnd_8169685 < baseStart_8169685 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169687 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 7]
def baseStart_8169687 : Nat := 118140960795 + 8169687 * 2 ^ 59
def prefixEnd_8169687 : Nat := 4983230072969 + 3 ^ 40 * 8169687 * 2
def baseEnd_8169687 : Nat := 4194976227788282795740799

theorem tailTrace_8169687 : CollatzResearch.WordTrace tailWord_8169687 prefixEnd_8169687 4194976227788282795740799 := by
  unfold tailWord_8169687
  simp only [CollatzResearch.WordTrace]
  refine ⟨297972964353626745301475315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198648642902417830200983543 297972964353626745301475315)
  ·
    refine ⟨446959446530440117952212973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297972964353626745301475315 446959446530440117952212973)
    ·
      refine ⟨167609792448915044232079865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 446959446530440117952212973 167609792448915044232079865)
      ·
        refine ⟨125707344336686283174059899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167609792448915044232079865 125707344336686283174059899)
        ·
          refine ⟨188561016505029424761089849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125707344336686283174059899 188561016505029424761089849)
          ·
            refine ⟨141420762378772068570817387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188561016505029424761089849 141420762378772068570817387)
            ·
              refine ⟨212131143568158102856226081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141420762378772068570817387 212131143568158102856226081)
              ·
                refine ⟨159098357676118577142169561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212131143568158102856226081 159098357676118577142169561)
                ·
                  refine ⟨119323768257088932856627171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159098357676118577142169561 119323768257088932856627171)
                  ·
                    refine ⟨178985652385633399284940757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 119323768257088932856627171 178985652385633399284940757)
                    ·
                      refine ⟨4194976227788282795740799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 178985652385633399284940757 4194976227788282795740799)
                      ·
                        rfl

theorem cell23_8169687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_8169687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169687 prefixEnd_8169687 := by exact prefixLift 8169687
  have htrace : WordTrace (prefixWord ++ tailWord_8169687) baseStart_8169687 baseEnd_8169687 := by
    simpa [prefixWord, tailWord_8169687, baseEnd_8169687] using wordTrace_append hprefix tailTrace_8169687
  have hstable : (prefixWord ++ tailWord_8169687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169687).length < 2 ^ (prefixWord ++ tailWord_8169687).sum := by decide
  have hdescent : baseEnd_8169687 < baseStart_8169687 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169711 : List Nat := [1, 1, 2, 1, 6, 1, 3, 2, 1, 5]
def baseStart_8169711 : Nat := 118140960795 + 8169711 * 2 ^ 59
def prefixEnd_8169711 : Nat := 4983230072969 + 3 ^ 40 * 8169711 * 2
def baseEnd_8169711 : Nat := 1398329517107996900613563

theorem tailTrace_8169711 : CollatzResearch.WordTrace tailWord_8169711 prefixEnd_8169711 1398329517107996900613563 := by
  unfold tailWord_8169711
  simp only [CollatzResearch.WordTrace]
  refine ⟨297973839705539797400348987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198649226470359864933565991 297973839705539797400348987)
  ·
    refine ⟨446960759558309696100523481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297973839705539797400348987 446960759558309696100523481)
    ·
      refine ⟨335220569668732272075392611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446960759558309696100523481 335220569668732272075392611)
      ·
        refine ⟨502830854503098408113088917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335220569668732272075392611 502830854503098408113088917)
        ·
          refine ⟨23570196304832737880301043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 502830854503098408113088917 23570196304832737880301043)
          ·
            refine ⟨35355294457249106820451565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23570196304832737880301043 35355294457249106820451565)
            ·
              refine ⟨13258235421468415057669337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35355294457249106820451565 13258235421468415057669337)
              ·
                refine ⟨9943676566101311293252003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13258235421468415057669337 9943676566101311293252003)
                ·
                  refine ⟨14915514849151966939878005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9943676566101311293252003 14915514849151966939878005)
                  ·
                    refine ⟨1398329517107996900613563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14915514849151966939878005 1398329517107996900613563)
                    ·
                      rfl

theorem cell23_8169711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2, 1, 5].length) (baseStart_8169711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169711 prefixEnd_8169711 := by exact prefixLift 8169711
  have htrace : WordTrace (prefixWord ++ tailWord_8169711) baseStart_8169711 baseEnd_8169711 := by
    simpa [prefixWord, tailWord_8169711, baseEnd_8169711] using wordTrace_append hprefix tailTrace_8169711
  have hstable : (prefixWord ++ tailWord_8169711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169711).length < 2 ^ (prefixWord ++ tailWord_8169711).sum := by decide
  have hdescent : baseEnd_8169711 < baseStart_8169711 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169718 : List Nat := [5, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2]
def baseStart_8169718 : Nat := 118140960795 + 8169718 * 2 ^ 59
def prefixEnd_8169718 : Nat := 4983230072969 + 3 ^ 40 * 8169718 * 2
def baseEnd_8169718 : Nat := 4194992145688572174453157

theorem tailTrace_8169718 : CollatzResearch.WordTrace tailWord_8169718 prefixEnd_8169718 4194992145688572174453157 := by
  unfold tailWord_8169718
  simp only [CollatzResearch.WordTrace]
  refine ⟨18623380938532152349740863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198649396677676291730569205 18623380938532152349740863)
  ·
    refine ⟨27935071407798228524611295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18623380938532152349740863 27935071407798228524611295)
    ·
      refine ⟨41902607111697342786916943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27935071407798228524611295 41902607111697342786916943)
      ·
        refine ⟨62853910667546014180375415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41902607111697342786916943 62853910667546014180375415)
        ·
          refine ⟨94280866001319021270563123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62853910667546014180375415 94280866001319021270563123)
          ·
            refine ⟨141421299001978531905844685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94280866001319021270563123 141421299001978531905844685)
            ·
              refine ⟨53032987125741949464691757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141421299001978531905844685 53032987125741949464691757)
              ·
                refine ⟨19887370172153231049259409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53032987125741949464691757 19887370172153231049259409)
                ·
                  refine ⟨14915527629114923286944557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19887370172153231049259409 14915527629114923286944557)
                  ·
                    refine ⟨5593322860918096232604209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14915527629114923286944557 5593322860918096232604209)
                    ·
                      refine ⟨4194992145688572174453157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5593322860918096232604209 4194992145688572174453157)
                      ·
                        rfl

theorem cell23_8169718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2].length) (baseStart_8169718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169718 prefixEnd_8169718 := by exact prefixLift 8169718
  have htrace : WordTrace (prefixWord ++ tailWord_8169718) baseStart_8169718 baseEnd_8169718 := by
    simpa [prefixWord, tailWord_8169718, baseEnd_8169718] using wordTrace_append hprefix tailTrace_8169718
  have hstable : (prefixWord ++ tailWord_8169718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169718).length < 2 ^ (prefixWord ++ tailWord_8169718).sum := by decide
  have hdescent : baseEnd_8169718 < baseStart_8169718 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169724 : List Nat := [2, 2, 2, 1, 4, 1, 1, 1, 3, 6]
def baseStart_8169724 : Nat := 118140960795 + 8169724 * 2 ^ 59
def prefixEnd_8169724 : Nat := 4983230072969 + 3 ^ 40 * 8169724 * 2
def baseEnd_8169724 : Nat := 1398331742190833050326043

theorem tailTrace_8169724 : CollatzResearch.WordTrace tailWord_8169724 prefixEnd_8169724 1398331742190833050326043 := by
  unfold tailWord_8169724
  simp only [CollatzResearch.WordTrace]
  refine ⟨148987156927246350310286113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198649542569661800413714817 148987156927246350310286113)
  ·
    refine ⟨111740367695434762732714585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148987156927246350310286113 111740367695434762732714585)
    ·
      refine ⟨83805275771576072049535939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111740367695434762732714585 83805275771576072049535939)
      ·
        refine ⟨125707913657364108074303909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83805275771576072049535939 125707913657364108074303909)
        ·
          refine ⟨23570233810755770263931983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125707913657364108074303909 23570233810755770263931983)
          ·
            refine ⟨35355350716133655395897975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23570233810755770263931983 35355350716133655395897975)
            ·
              refine ⟨53033026074200483093846963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35355350716133655395897975 53033026074200483093846963)
              ·
                refine ⟨79549539111300724640770445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53033026074200483093846963 79549539111300724640770445)
                ·
                  refine ⟨29831077166737771740288917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79549539111300724640770445 29831077166737771740288917)
                  ·
                    refine ⟨1398331742190833050326043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29831077166737771740288917 1398331742190833050326043)
                    ·
                      rfl

theorem cell23_8169724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_8169724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169724 prefixEnd_8169724 := by exact prefixLift 8169724
  have htrace : WordTrace (prefixWord ++ tailWord_8169724) baseStart_8169724 baseEnd_8169724 := by
    simpa [prefixWord, tailWord_8169724, baseEnd_8169724] using wordTrace_append hprefix tailTrace_8169724
  have hstable : (prefixWord ++ tailWord_8169724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169724).length < 2 ^ (prefixWord ++ tailWord_8169724).sum := by decide
  have hdescent : baseEnd_8169724 < baseStart_8169724 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169737 : List Nat := [1, 2, 1, 1, 3, 15]
def baseStart_8169737 : Nat := 118140960795 + 8169737 * 2 ^ 59
def prefixEnd_8169737 : Nat := 4983230072969 + 3 ^ 40 * 8169737 * 2
def baseEnd_8169737 : Nat := 17263382312020607407883

theorem tailTrace_8169737 : CollatzResearch.WordTrace tailWord_8169737 prefixEnd_8169737 17263382312020607407883 := by
  unfold tailWord_8169737
  simp only [CollatzResearch.WordTrace]
  refine ⟨297974788003445603840795465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198649858668963735893863643 297974788003445603840795465)
  ·
    refine ⟨223481091002584202880596599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297974788003445603840795465 223481091002584202880596599)
    ·
      refine ⟨335221636503876304320894899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223481091002584202880596599 335221636503876304320894899)
      ·
        refine ⟨502832454755814456481342349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335221636503876304320894899 502832454755814456481342349)
        ·
          refine ⟨188562170533430421180503381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 502832454755814456481342349 188562170533430421180503381)
          ·
            refine ⟨17263382312020607407883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 188562170533430421180503381 17263382312020607407883)
            ·
              rfl

theorem cell23_8169737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 15].length) (baseStart_8169737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169737 prefixEnd_8169737 := by exact prefixLift 8169737
  have htrace : WordTrace (prefixWord ++ tailWord_8169737) baseStart_8169737 baseEnd_8169737 := by
    simpa [prefixWord, tailWord_8169737, baseEnd_8169737] using wordTrace_append hprefix tailTrace_8169737
  have hstable : (prefixWord ++ tailWord_8169737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169737).length < 2 ^ (prefixWord ++ tailWord_8169737).sum := by decide
  have hdescent : baseEnd_8169737 < baseStart_8169737 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169751 : List Nat := [1, 1, 3, 4, 1, 2, 1, 2, 3, 2, 3]
def baseStart_8169751 : Nat := 118140960795 + 8169751 * 2 ^ 59
def prefixEnd_8169751 : Nat := 4983230072969 + 3 ^ 40 * 8169751 * 2
def baseEnd_8169751 : Nat := 4195009090550170545340505

theorem tailTrace_8169751 : CollatzResearch.WordTrace tailWord_8169751 prefixEnd_8169751 4195009090550170545340505 := by
  unfold tailWord_8169751
  simp only [CollatzResearch.WordTrace]
  refine ⟨297975298625394884231805107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198650199083596589487870071 297975298625394884231805107)
  ·
    refine ⟨446962947938092326347707661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297975298625394884231805107 446962947938092326347707661)
    ·
      refine ⟨167611105476784622380390373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 446962947938092326347707661 167611105476784622380390373)
      ·
        refine ⟨31427082276897116696323195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167611105476784622380390373 31427082276897116696323195)
        ·
          refine ⟨47140623415345675044484793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31427082276897116696323195 47140623415345675044484793)
          ·
            refine ⟨35355467561509256283363595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47140623415345675044484793 35355467561509256283363595)
            ·
              refine ⟨53033201342263884425045393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35355467561509256283363595 53033201342263884425045393)
              ·
                refine ⟨39774901006697913318784045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53033201342263884425045393 39774901006697913318784045)
                ·
                  refine ⟨14915587877511717494544017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39774901006697913318784045 14915587877511717494544017)
                  ·
                    refine ⟨11186690908133788120908013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14915587877511717494544017 11186690908133788120908013)
                    ·
                      refine ⟨4195009090550170545340505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11186690908133788120908013 4195009090550170545340505)
                      ·
                        rfl

theorem cell23_8169751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_8169751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169751 prefixEnd_8169751 := by exact prefixLift 8169751
  have htrace : WordTrace (prefixWord ++ tailWord_8169751) baseStart_8169751 baseEnd_8169751 := by
    simpa [prefixWord, tailWord_8169751, baseEnd_8169751] using wordTrace_append hprefix tailTrace_8169751
  have hstable : (prefixWord ++ tailWord_8169751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169751).length < 2 ^ (prefixWord ++ tailWord_8169751).sum := by decide
  have hdescent : baseEnd_8169751 < baseStart_8169751 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169758 : List Nat := [4, 3, 2, 1, 1, 1, 1, 3, 1, 6]
def baseStart_8169758 : Nat := 118140960795 + 8169758 * 2 ^ 59
def prefixEnd_8169758 : Nat := 4983230072969 + 3 ^ 40 * 8169758 * 2
def baseEnd_8169758 : Nat := 1398337561638250672650991

theorem tailTrace_8169758 : CollatzResearch.WordTrace tailWord_8169758 prefixEnd_8169758 1398337561638250672650991 := by
  unfold tailWord_8169758
  simp only [CollatzResearch.WordTrace]
  refine ⟨37246944242046190553413741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198650369290913016284873285 37246944242046190553413741)
  ·
    refine ⟨13967604090767321457530153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37246944242046190553413741 13967604090767321457530153)
    ·
      refine ⟨10475703068075491093147615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13967604090767321457530153 10475703068075491093147615)
      ·
        refine ⟨15713554602113236639721423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10475703068075491093147615 15713554602113236639721423)
        ·
          refine ⟨23570331903169854959582135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15713554602113236639721423 23570331903169854959582135)
          ·
            refine ⟨35355497854754782439373203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23570331903169854959582135 35355497854754782439373203)
            ·
              refine ⟨53033246782132173659059805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35355497854754782439373203 53033246782132173659059805)
              ·
                refine ⟨19887467543299565122147427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53033246782132173659059805 19887467543299565122147427)
                ·
                  refine ⟨29831201314949347683221141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19887467543299565122147427 29831201314949347683221141)
                  ·
                    refine ⟨1398337561638250672650991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29831201314949347683221141 1398337561638250672650991)
                    ·
                      rfl

theorem cell23_8169758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_8169758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169758 prefixEnd_8169758 := by exact prefixLift 8169758
  have htrace : WordTrace (prefixWord ++ tailWord_8169758) baseStart_8169758 baseEnd_8169758 := by
    simpa [prefixWord, tailWord_8169758, baseEnd_8169758] using wordTrace_append hprefix tailTrace_8169758
  have hstable : (prefixWord ++ tailWord_8169758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169758).length < 2 ^ (prefixWord ++ tailWord_8169758).sum := by decide
  have hdescent : baseEnd_8169758 < baseStart_8169758 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169765 : List Nat := [1, 3, 1, 2, 5, 1, 1, 2, 3, 2, 2]
def baseStart_8169765 : Nat := 118140960795 + 8169765 * 2 ^ 59
def prefixEnd_8169765 : Nat := 4983230072969 + 3 ^ 40 * 8169765 * 2
def baseEnd_8169765 : Nat := 4195016279279333490565441

theorem tailTrace_8169765 : CollatzResearch.WordTrace tailWord_8169765 prefixEnd_8169765 4195016279279333490565441 := by
  unfold tailWord_8169765
  simp only [CollatzResearch.WordTrace]
  refine ⟨297975809247344164622814749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198650539498229443081876499 297975809247344164622814749)
  ·
    refine ⟨111740928467754061733555531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297975809247344164622814749 111740928467754061733555531)
    ·
      refine ⟨167611392701631092600333297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111740928467754061733555531 167611392701631092600333297)
      ·
        refine ⟨125708544526223319450249973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167611392701631092600333297 125708544526223319450249973)
        ·
          refine ⟨11785176049333436198460935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125708544526223319450249973 11785176049333436198460935)
          ·
            refine ⟨17677764074000154297691403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11785176049333436198460935 17677764074000154297691403)
            ·
              refine ⟨26516646111000231446537105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17677764074000154297691403 26516646111000231446537105)
              ·
                refine ⟨19887484583250173584902829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26516646111000231446537105 19887484583250173584902829)
                ·
                  refine ⟨7457806718718815094338561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19887484583250173584902829 7457806718718815094338561)
                  ·
                    refine ⟨5593355039039111320753921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7457806718718815094338561 5593355039039111320753921)
                    ·
                      refine ⟨4195016279279333490565441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5593355039039111320753921 4195016279279333490565441)
                      ·
                        rfl

theorem cell23_8169765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 3, 2, 2].length) (baseStart_8169765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169765 prefixEnd_8169765 := by exact prefixLift 8169765
  have htrace : WordTrace (prefixWord ++ tailWord_8169765) baseStart_8169765 baseEnd_8169765 := by
    simpa [prefixWord, tailWord_8169765, baseEnd_8169765] using wordTrace_append hprefix tailTrace_8169765
  have hstable : (prefixWord ++ tailWord_8169765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169765).length < 2 ^ (prefixWord ++ tailWord_8169765).sum := by decide
  have hdescent : baseEnd_8169765 < baseStart_8169765 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169781 : List Nat := [1, 3, 3, 1, 2, 1, 1, 4, 1, 3, 3]
def baseStart_8169781 : Nat := 118140960795 + 8169781 * 2 ^ 59
def prefixEnd_8169781 : Nat := 4983230072969 + 3 ^ 40 * 8169781 * 2
def baseEnd_8169781 : Nat := 4195024494969805427965367

theorem tailTrace_8169781 : CollatzResearch.WordTrace tailWord_8169781 prefixEnd_8169781 4195024494969805427965367 := by
  unfold tailWord_8169781
  simp only [CollatzResearch.WordTrace]
  refine ⟨297976392815286199355397197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198650928543524132903598131 297976392815286199355397197)
  ·
    refine ⟨111741147305732324758273949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297976392815286199355397197 111741147305732324758273949)
    ·
      refine ⟨41902930239649621784352731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111741147305732324758273949 41902930239649621784352731)
      ·
        refine ⟨62854395359474432676529097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41902930239649621784352731 62854395359474432676529097)
        ·
          refine ⟨47140796519605824507396823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62854395359474432676529097 47140796519605824507396823)
          ·
            refine ⟨70711194779408736761095235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47140796519605824507396823 70711194779408736761095235)
            ·
              refine ⟨106066792169113105141642853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70711194779408736761095235 106066792169113105141642853)
              ·
                refine ⟨19887523531708707214058035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106066792169113105141642853 19887523531708707214058035)
                ·
                  refine ⟨29831285297563060821087053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19887523531708707214058035 29831285297563060821087053)
                  ·
                    refine ⟨11186731986586147807907645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29831285297563060821087053 11186731986586147807907645)
                    ·
                      refine ⟨4195024494969805427965367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11186731986586147807907645 4195024494969805427965367)
                      ·
                        rfl

theorem cell23_8169781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_8169781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169781 prefixEnd_8169781 := by exact prefixLift 8169781
  have htrace : WordTrace (prefixWord ++ tailWord_8169781) baseStart_8169781 baseEnd_8169781 := by
    simpa [prefixWord, tailWord_8169781, baseEnd_8169781] using wordTrace_append hprefix tailTrace_8169781
  have hstable : (prefixWord ++ tailWord_8169781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169781).length < 2 ^ (prefixWord ++ tailWord_8169781).sum := by decide
  have hdescent : baseEnd_8169781 < baseStart_8169781 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169785 : List Nat := [1, 2, 1, 6, 1, 1, 4, 1, 1, 2, 3]
def baseStart_8169785 : Nat := 118140960795 + 8169785 * 2 ^ 59
def prefixEnd_8169785 : Nat := 4983230072969 + 3 ^ 40 * 8169785 * 2
def baseEnd_8169785 : Nat := 4195026548892423412315349

theorem tailTrace_8169785 : CollatzResearch.WordTrace tailWord_8169785 prefixEnd_8169785 4195026548892423412315349 := by
  unfold tailWord_8169785
  simp only [CollatzResearch.WordTrace]
  refine ⟨297976538707271708038542809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198651025804847805359028539 297976538707271708038542809)
  ·
    refine ⟨223482404030453781028907107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297976538707271708038542809 223482404030453781028907107)
    ·
      refine ⟨335223606045680671543360661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223482404030453781028907107 335223606045680671543360661)
      ·
        refine ⟨15713606533391281478595031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 335223606045680671543360661 15713606533391281478595031)
        ·
          refine ⟨23570409800086922217892547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15713606533391281478595031 23570409800086922217892547)
          ·
            refine ⟨35355614700130383326838821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23570409800086922217892547 35355614700130383326838821)
            ·
              refine ⟨6629177756274446873782279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35355614700130383326838821 6629177756274446873782279)
              ·
                refine ⟨9943766634411670310673419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6629177756274446873782279 9943766634411670310673419)
                ·
                  refine ⟨14915649951617505466010129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9943766634411670310673419 14915649951617505466010129)
                  ·
                    refine ⟨11186737463713129099507597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14915649951617505466010129 11186737463713129099507597)
                    ·
                      refine ⟨4195026548892423412315349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11186737463713129099507597 4195026548892423412315349)
                      ·
                        rfl

theorem cell23_8169785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_8169785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169785 prefixEnd_8169785 := by exact prefixLift 8169785
  have htrace : WordTrace (prefixWord ++ tailWord_8169785) baseStart_8169785 baseEnd_8169785 := by
    simpa [prefixWord, tailWord_8169785, baseEnd_8169785] using wordTrace_append hprefix tailTrace_8169785
  have hstable : (prefixWord ++ tailWord_8169785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169785).length < 2 ^ (prefixWord ++ tailWord_8169785).sum := by decide
  have hdescent : baseEnd_8169785 < baseStart_8169785 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169815 : List Nat := [1, 1, 3, 2, 3, 1, 5, 1, 2, 1, 3]
def baseStart_8169815 : Nat := 118140960795 + 8169815 * 2 ^ 59
def prefixEnd_8169815 : Nat := 4983230072969 + 3 ^ 40 * 8169815 * 2
def baseEnd_8169815 : Nat := 4195041953312058294940211

theorem tailTrace_8169815 : CollatzResearch.WordTrace tailWord_8169815 prefixEnd_8169815 4195041953312058294940211 := by
  unfold tailWord_8169815
  simp only [CollatzResearch.WordTrace]
  refine ⟨297977632897163023162134899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198651755264775348774756599 297977632897163023162134899)
  ·
    refine ⟨446966449345744534743202349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297977632897163023162134899 446966449345744534743202349)
    ·
      refine ⟨167612418504654200528700881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 446966449345744534743202349 167612418504654200528700881)
      ·
        refine ⟨125709313878490650396525661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167612418504654200528700881 125709313878490650396525661)
        ·
          refine ⟨47140992704433993898697123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125709313878490650396525661 47140992704433993898697123)
          ·
            refine ⟨70711489056650990848045685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47140992704433993898697123 70711489056650990848045685)
            ·
              refine ⟨6629202099061030392004283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70711489056650990848045685 6629202099061030392004283)
              ·
                refine ⟨9943803148591545588006425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6629202099061030392004283 9943803148591545588006425)
                ·
                  refine ⟨7457852361443659191004819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9943803148591545588006425 7457852361443659191004819)
                  ·
                    refine ⟨11186778542165488786507229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7457852361443659191004819 11186778542165488786507229)
                    ·
                      refine ⟨4195041953312058294940211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11186778542165488786507229 4195041953312058294940211)
                      ·
                        rfl

theorem cell23_8169815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 1, 2, 1, 3].length) (baseStart_8169815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169815 prefixEnd_8169815 := by exact prefixLift 8169815
  have htrace : WordTrace (prefixWord ++ tailWord_8169815) baseStart_8169815 baseEnd_8169815 := by
    simpa [prefixWord, tailWord_8169815, baseEnd_8169815] using wordTrace_append hprefix tailTrace_8169815
  have hstable : (prefixWord ++ tailWord_8169815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169815).length < 2 ^ (prefixWord ++ tailWord_8169815).sum := by decide
  have hdescent : baseEnd_8169815 < baseStart_8169815 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169822 : List Nat := [4, 4, 2, 1, 1, 1, 1, 9]
def baseStart_8169822 : Nat := 118140960795 + 8169822 * 2 ^ 59
def prefixEnd_8169822 : Nat := 4983230072969 + 3 ^ 40 * 8169822 * 2
def baseEnd_8169822 : Nat := 155372057321357028427877

theorem tailTrace_8169822 : CollatzResearch.WordTrace tailWord_8169822 prefixEnd_8169822 155372057321357028427877 := by
  unfold tailWord_8169822
  simp only [CollatzResearch.WordTrace]
  refine ⟨37247236026017207919704965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198651925472091775571759813 37247236026017207919704965)
  ·
    refine ⟨6983856754878226484944681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37247236026017207919704965 6983856754878226484944681)
    ·
      refine ⟨5237892566158669863708511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6983856754878226484944681 5237892566158669863708511)
      ·
        refine ⟨7856838849238004795562767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5237892566158669863708511 7856838849238004795562767)
        ·
          refine ⟨11785258273857007193344151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7856838849238004795562767 11785258273857007193344151)
          ·
            refine ⟨17677887410785510790016227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11785258273857007193344151 17677887410785510790016227)
            ·
              refine ⟨26516831116178266185024341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17677887410785510790016227 26516831116178266185024341)
              ·
                refine ⟨155372057321357028427877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26516831116178266185024341 155372057321357028427877)
                ·
                  rfl

theorem cell23_8169822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 9].length) (baseStart_8169822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169822 prefixEnd_8169822 := by exact prefixLift 8169822
  have htrace : WordTrace (prefixWord ++ tailWord_8169822) baseStart_8169822 baseEnd_8169822 := by
    simpa [prefixWord, tailWord_8169822, baseEnd_8169822] using wordTrace_append hprefix tailTrace_8169822
  have hstable : (prefixWord ++ tailWord_8169822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169822).length < 2 ^ (prefixWord ++ tailWord_8169822).sum := by decide
  have hdescent : baseEnd_8169822 < baseStart_8169822 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169866 : List Nat := [3, 1, 2, 5, 2, 1, 2, 1, 2, 1, 3]
def baseStart_8169866 : Nat := 118140960795 + 8169866 * 2 ^ 59
def prefixEnd_8169866 : Nat := 4983230072969 + 3 ^ 40 * 8169866 * 2
def baseEnd_8169866 : Nat := 4195068140825437595402477

theorem tailTrace_8169866 : CollatzResearch.WordTrace tailWord_8169866 prefixEnd_8169866 4195068140825437595402477 := by
  unfold tailWord_8169866
  simp only [CollatzResearch.WordTrace]
  refine ⟨74494873254994564718060363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198652995346652172581494301 74494873254994564718060363)
  ·
    refine ⟨111742309882491847077090545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74494873254994564718060363 111742309882491847077090545)
    ·
      refine ⟨83806732411868885307817909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111742309882491847077090545 83806732411868885307817909)
      ·
        refine ⟨7856881163612707997607929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83806732411868885307817909 7856881163612707997607929)
        ·
          refine ⟨5892660872709530998205947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7856881163612707997607929 5892660872709530998205947)
          ·
            refine ⟨8838991309064296497308921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5892660872709530998205947 8838991309064296497308921)
            ·
              refine ⟨6629243481798222372981691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8838991309064296497308921 6629243481798222372981691)
              ·
                refine ⟨9943865222697333559472537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6629243481798222372981691 9943865222697333559472537)
                ·
                  refine ⟨7457898917023000169604403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9943865222697333559472537 7457898917023000169604403)
                  ·
                    refine ⟨11186848375534500254406605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7457898917023000169604403 11186848375534500254406605)
                    ·
                      refine ⟨4195068140825437595402477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11186848375534500254406605 4195068140825437595402477)
                      ·
                        rfl

theorem cell23_8169866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_8169866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169866 prefixEnd_8169866 := by exact prefixLift 8169866
  have htrace : WordTrace (prefixWord ++ tailWord_8169866) baseStart_8169866 baseEnd_8169866 := by
    simpa [prefixWord, tailWord_8169866, baseEnd_8169866] using wordTrace_append hprefix tailTrace_8169866
  have hstable : (prefixWord ++ tailWord_8169866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169866).length < 2 ^ (prefixWord ++ tailWord_8169866).sum := by decide
  have hdescent : baseEnd_8169866 < baseStart_8169866 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169891 : List Nat := [1, 1, 1, 4, 1, 4, 1, 3, 2, 5]
def baseStart_8169891 : Nat := 118140960795 + 8169891 * 2 ^ 59
def prefixEnd_8169891 : Nat := 4983230072969 + 3 ^ 40 * 8169891 * 2
def baseEnd_8169891 : Nat := 1398360325947266665863287

theorem tailTrace_8169891 : CollatzResearch.WordTrace tailWord_8169891 prefixEnd_8169891 1398360325947266665863287 := by
  unfold tailWord_8169891
  simp only [CollatzResearch.WordTrace]
  refine ⟨297980404844887688141901527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198653603229925125427934351 297980404844887688141901527)
  ·
    refine ⟨446970607267331532212852291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297980404844887688141901527 446970607267331532212852291)
    ·
      refine ⟨670455910900997298319278437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446970607267331532212852291 670455910900997298319278437)
      ·
        refine ⟨125710483293936993434864707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 670455910900997298319278437 125710483293936993434864707)
        ·
          refine ⟨188565724940905490152297061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125710483293936993434864707 188565724940905490152297061)
          ·
            refine ⟨35356073426419779403555699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188565724940905490152297061 35356073426419779403555699)
            ·
              refine ⟨53034110139629669105333549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35356073426419779403555699 53034110139629669105333549)
              ·
                refine ⟨19887791302361125914500081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53034110139629669105333549 19887791302361125914500081)
                ·
                  refine ⟨14915843476770844435875061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19887791302361125914500081 14915843476770844435875061)
                  ·
                    refine ⟨1398360325947266665863287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14915843476770844435875061 1398360325947266665863287)
                    ·
                      rfl

theorem cell23_8169891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2, 5].length) (baseStart_8169891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169891 prefixEnd_8169891 := by exact prefixLift 8169891
  have htrace : WordTrace (prefixWord ++ tailWord_8169891) baseStart_8169891 baseEnd_8169891 := by
    simpa [prefixWord, tailWord_8169891, baseEnd_8169891] using wordTrace_append hprefix tailTrace_8169891
  have hstable : (prefixWord ++ tailWord_8169891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169891).length < 2 ^ (prefixWord ++ tailWord_8169891).sum := by decide
  have hdescent : baseEnd_8169891 < baseStart_8169891 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169904 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 4, 8]
def baseStart_8169904 : Nat := 118140960795 + 8169904 * 2 ^ 59
def prefixEnd_8169904 : Nat := 4983230072969 + 3 ^ 40 * 8169904 * 2
def baseEnd_8169904 : Nat := 1398362551030102815575767

theorem tailTrace_8169904 : CollatzResearch.WordTrace tailWord_8169904 prefixEnd_8169904 1398362551030102815575767 := by
  unfold tailWord_8169904
  simp only [CollatzResearch.WordTrace]
  refine ⟨148990439496920295681062383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198653919329227060908083177 148990439496920295681062383)
  ·
    refine ⟨223485659245380443521593575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148990439496920295681062383 223485659245380443521593575)
    ·
      refine ⟨335228488868070665282390363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223485659245380443521593575 335228488868070665282390363)
      ·
        refine ⟨502842733302105997923585545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335228488868070665282390363 502842733302105997923585545)
        ·
          refine ⟨377132049976579498442689159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 502842733302105997923585545 377132049976579498442689159)
          ·
            refine ⟨565698074964869247664033739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377132049976579498442689159 565698074964869247664033739)
            ·
              refine ⟨848547112447303871496050609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 565698074964869247664033739 848547112447303871496050609)
              ·
                refine ⟨636410334335477903622037957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 848547112447303871496050609 636410334335477903622037957)
                ·
                  refine ⟨119326937687902106929132117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 636410334335477903622037957 119326937687902106929132117)
                  ·
                    refine ⟨1398362551030102815575767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119326937687902106929132117 1398362551030102815575767)
                    ·
                      rfl

theorem cell23_8169904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 4, 8].length) (baseStart_8169904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169904 prefixEnd_8169904 := by exact prefixLift 8169904
  have htrace : WordTrace (prefixWord ++ tailWord_8169904) baseStart_8169904 baseEnd_8169904 := by
    simpa [prefixWord, tailWord_8169904, baseEnd_8169904] using wordTrace_append hprefix tailTrace_8169904
  have hstable : (prefixWord ++ tailWord_8169904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169904).length < 2 ^ (prefixWord ++ tailWord_8169904).sum := by decide
  have hdescent : baseEnd_8169904 < baseStart_8169904 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169928 : List Nat := [2, 1, 3, 1, 3, 2, 1, 1, 1, 6, 2]
def baseStart_8169928 : Nat := 118140960795 + 8169928 * 2 ^ 59
def prefixEnd_8169928 : Nat := 4983230072969 + 3 ^ 40 * 8169928 * 2
def baseEnd_8169928 : Nat := 4195099976626016352827191

theorem tailTrace_8169928 : CollatzResearch.WordTrace tailWord_8169928 prefixEnd_8169928 4195099976626016352827191 := by
  unfold tailWord_8169928
  simp only [CollatzResearch.WordTrace]
  refine ⟨148990877172876821730499219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198654502897169095640665625 148990877172876821730499219)
  ·
    refine ⟨223486315759315232595748829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148990877172876821730499219 223486315759315232595748829)
    ·
      refine ⟨83807368409743212223405811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223486315759315232595748829 83807368409743212223405811)
      ·
        refine ⟨125711052614614818335108717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83807368409743212223405811 125711052614614818335108717)
        ·
          refine ⟨47141644730480556875665769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125711052614614818335108717 47141644730480556875665769)
          ·
            refine ⟨35356233547860417656749327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47141644730480556875665769 35356233547860417656749327)
            ·
              refine ⟨53034350321790626485123991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35356233547860417656749327 53034350321790626485123991)
              ·
                refine ⟨79551525482685939727685987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53034350321790626485123991 79551525482685939727685987)
                ·
                  refine ⟨119327288224028909591528981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79551525482685939727685987 119327288224028909591528981)
                  ·
                    refine ⟨5593466635501355137102921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 119327288224028909591528981 5593466635501355137102921)
                    ·
                      refine ⟨4195099976626016352827191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5593466635501355137102921 4195099976626016352827191)
                      ·
                        rfl

theorem cell23_8169928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 1, 6, 2].length) (baseStart_8169928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169928 prefixEnd_8169928 := by exact prefixLift 8169928
  have htrace : WordTrace (prefixWord ++ tailWord_8169928) baseStart_8169928 baseEnd_8169928 := by
    simpa [prefixWord, tailWord_8169928, baseEnd_8169928] using wordTrace_append hprefix tailTrace_8169928
  have hstable : (prefixWord ++ tailWord_8169928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169928).length < 2 ^ (prefixWord ++ tailWord_8169928).sum := by decide
  have hdescent : baseEnd_8169928 < baseStart_8169928 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169931 : List Nat := [1, 1, 1, 1, 3, 3, 1, 4, 1, 4, 3]
def baseStart_8169931 : Nat := 118140960795 + 8169931 * 2 ^ 59
def prefixEnd_8169931 : Nat := 4983230072969 + 3 ^ 40 * 8169931 * 2
def baseEnd_8169931 : Nat := 4195101517067979841089677

theorem tailTrace_8169931 : CollatzResearch.WordTrace tailWord_8169931 prefixEnd_8169931 4195101517067979841089677 := by
  unfold tailWord_8169931
  simp only [CollatzResearch.WordTrace]
  refine ⟨297981863764742774973357647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198654575843161849982238431 297981863764742774973357647)
  ·
    refine ⟨446972795647114162460036471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297981863764742774973357647 446972795647114162460036471)
    ·
      refine ⟨670459193470671243690054707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446972795647114162460036471 670459193470671243690054707)
      ·
        refine ⟨1005688790206006865535082061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 670459193470671243690054707 1005688790206006865535082061)
        ·
          refine ⟨377133296327252574575655773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1005688790206006865535082061 377133296327252574575655773)
          ·
            refine ⟨141424986122719715465870915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 377133296327252574575655773 141424986122719715465870915)
            ·
              refine ⟨212137479184079573198806373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141424986122719715465870915 212137479184079573198806373)
              ·
                refine ⟨39775777347014919974776195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 212137479184079573198806373 39775777347014919974776195)
                ·
                  refine ⟨59663666020522379962164293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39775777347014919974776195 59663666020522379962164293)
                  ·
                    refine ⟨11186937378847946242905805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59663666020522379962164293 11186937378847946242905805)
                    ·
                      refine ⟨4195101517067979841089677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11186937378847946242905805 4195101517067979841089677)
                      ·
                        rfl

theorem cell23_8169931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 4, 3].length) (baseStart_8169931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169931 prefixEnd_8169931 := by exact prefixLift 8169931
  have htrace : WordTrace (prefixWord ++ tailWord_8169931) baseStart_8169931 baseEnd_8169931 := by
    simpa [prefixWord, tailWord_8169931, baseEnd_8169931] using wordTrace_append hprefix tailTrace_8169931
  have hstable : (prefixWord ++ tailWord_8169931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169931).length < 2 ^ (prefixWord ++ tailWord_8169931).sum := by decide
  have hdescent : baseEnd_8169931 < baseStart_8169931 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169985 : List Nat := [1, 2, 4, 1, 3, 2, 3, 1, 6]
def baseStart_8169985 : Nat := 118140960795 + 8169985 * 2 ^ 59
def prefixEnd_8169985 : Nat := 4983230072969 + 3 ^ 40 * 8169985 * 2
def baseEnd_8169985 : Nat := 466125471669258069979381

theorem tailTrace_8169985 : CollatzResearch.WordTrace tailWord_8169985 prefixEnd_8169985 466125471669258069979381 := by
  unfold tailWord_8169985
  simp only [CollatzResearch.WordTrace]
  refine ⟨297983833306547142195823409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198655888871031428130548939 297983833306547142195823409)
  ·
    refine ⟨223487874979910356646867557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297983833306547142195823409 223487874979910356646867557)
    ·
      refine ⟨41903976558733191871287667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223487874979910356646867557 41903976558733191871287667)
      ·
        refine ⟨62855964838099787806931501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41903976558733191871287667 62855964838099787806931501)
        ·
          refine ⟨23570986814287420427599313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62855964838099787806931501 23570986814287420427599313)
          ·
            refine ⟨17678240110715565320699485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23570986814287420427599313 17678240110715565320699485)
            ·
              refine ⟨6629340041518336995262307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17678240110715565320699485 6629340041518336995262307)
              ·
                refine ⟨9944010062277505492893461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6629340041518336995262307 9944010062277505492893461)
                ·
                  refine ⟨466125471669258069979381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9944010062277505492893461 466125471669258069979381)
                  ·
                    rfl

theorem cell23_8169985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 1, 6].length) (baseStart_8169985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169985 prefixEnd_8169985 := by exact prefixLift 8169985
  have htrace : WordTrace (prefixWord ++ tailWord_8169985) baseStart_8169985 baseEnd_8169985 := by
    simpa [prefixWord, tailWord_8169985, baseEnd_8169985] using wordTrace_append hprefix tailTrace_8169985
  have hstable : (prefixWord ++ tailWord_8169985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169985).length < 2 ^ (prefixWord ++ tailWord_8169985).sum := by decide
  have hdescent : baseEnd_8169985 < baseStart_8169985 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8169995 : List Nat := [1, 1, 1, 1, 7, 1, 2, 2, 3, 1, 3]
def baseStart_8169995 : Nat := 118140960795 + 8169995 * 2 ^ 59
def prefixEnd_8169995 : Nat := 4983230072969 + 3 ^ 40 * 8169995 * 2
def baseEnd_8169995 : Nat := 4195134379829867590689383

theorem tailTrace_8169995 : CollatzResearch.WordTrace tailWord_8169995 prefixEnd_8169995 4195134379829867590689383 := by
  unfold tailWord_8169995
  simp only [CollatzResearch.WordTrace]
  refine ⟨297984198036510913903687439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198656132024340609269124959 297984198036510913903687439)
  ·
    refine ⟨446976297054766370855531159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297984198036510913903687439 446976297054766370855531159)
    ·
      refine ⟨670464445582149556283296739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446976297054766370855531159 670464445582149556283296739)
      ·
        refine ⟨1005696668373224334424945109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 670464445582149556283296739 1005696668373224334424945109)
        ·
          refine ⟨23571015664997445338084651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 1005696668373224334424945109 23571015664997445338084651)
          ·
            refine ⟨35356523497496168007126977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23571015664997445338084651 35356523497496168007126977)
            ·
              refine ⟨26517392623122126005345233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35356523497496168007126977 26517392623122126005345233)
              ·
                refine ⟨19888044467341594504008925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26517392623122126005345233 19888044467341594504008925)
                ·
                  refine ⟨7458016675253097939003347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19888044467341594504008925 7458016675253097939003347)
                  ·
                    refine ⟨11187025012879646908505021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7458016675253097939003347 11187025012879646908505021)
                    ·
                      refine ⟨4195134379829867590689383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11187025012879646908505021 4195134379829867590689383)
                      ·
                        rfl

theorem cell23_8169995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 3, 1, 3].length) (baseStart_8169995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8169995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8169995 prefixEnd_8169995 := by exact prefixLift 8169995
  have htrace : WordTrace (prefixWord ++ tailWord_8169995) baseStart_8169995 baseEnd_8169995 := by
    simpa [prefixWord, tailWord_8169995, baseEnd_8169995] using wordTrace_append hprefix tailTrace_8169995
  have hstable : (prefixWord ++ tailWord_8169995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8169995).length < 2 ^ (prefixWord ++ tailWord_8169995).sum := by decide
  have hdescent : baseEnd_8169995 < baseStart_8169995 := by decide
  rcases family_descends (prefixWord ++ tailWord_8169995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8170005 : List Nat := [1, 3, 2, 1, 3, 1, 2, 3, 2, 3, 2]
def baseStart_8170005 : Nat := 118140960795 + 8170005 * 2 ^ 59
def prefixEnd_8170005 : Nat := 4983230072969 + 3 ^ 40 * 8170005 * 2
def baseEnd_8170005 : Nat := 4195139514636412551564337

theorem tailTrace_8170005 : CollatzResearch.WordTrace tailWord_8170005 prefixEnd_8170005 4195139514636412551564337 := by
  unfold tailWord_8170005
  simp only [CollatzResearch.WordTrace]
  refine ⟨297984562766474685611551469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198656375177649790407700979 297984562766474685611551469)
  ·
    refine ⟨111744211037428007104331801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297984562766474685611551469 111744211037428007104331801)
    ·
      refine ⟨83808158278071005328248851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111744211037428007104331801 83808158278071005328248851)
      ·
        refine ⟨125712237417106507992373277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83808158278071005328248851 125712237417106507992373277)
        ·
          refine ⟨47142089031414940497139979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125712237417106507992373277 47142089031414940497139979)
          ·
            refine ⟨70713133547122410745709969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47142089031414940497139979 70713133547122410745709969)
            ·
              refine ⟨53034850160341808059282477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70713133547122410745709969 53034850160341808059282477)
              ·
                refine ⟨19888068810128178022230929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53034850160341808059282477 19888068810128178022230929)
                ·
                  refine ⟨14916051607596133516673197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19888068810128178022230929 14916051607596133516673197)
                  ·
                    refine ⟨5593519352848550068752449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14916051607596133516673197 5593519352848550068752449)
                    ·
                      refine ⟨4195139514636412551564337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5593519352848550068752449 4195139514636412551564337)
                      ·
                        rfl

theorem cell23_8170005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2, 3, 2].length) (baseStart_8170005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8170005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8170005 prefixEnd_8170005 := by exact prefixLift 8170005
  have htrace : WordTrace (prefixWord ++ tailWord_8170005) baseStart_8170005 baseEnd_8170005 := by
    simpa [prefixWord, tailWord_8170005, baseEnd_8170005] using wordTrace_append hprefix tailTrace_8170005
  have hstable : (prefixWord ++ tailWord_8170005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8170005).length < 2 ^ (prefixWord ++ tailWord_8170005).sum := by decide
  have hdescent : baseEnd_8170005 < baseStart_8170005 := by decide
  rcases family_descends (prefixWord ++ tailWord_8170005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8170018 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 5, 1, 4]
def baseStart_8170018 : Nat := 118140960795 + 8170018 * 2 ^ 59
def prefixEnd_8170018 : Nat := 4983230072969 + 3 ^ 40 * 8170018 * 2
def baseEnd_8170018 : Nat := 4195146189884921000701777

theorem tailTrace_8170018 : CollatzResearch.WordTrace tailWord_8170018 prefixEnd_8170018 4195146189884921000701777 := by
  unfold tailWord_8170018
  simp only [CollatzResearch.WordTrace]
  refine ⟨74496259228856897207943677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198656691276951725887849805 74496259228856897207943677)
  ·
    refine ⟨27936097210821336452978879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74496259228856897207943677 27936097210821336452978879)
    ·
      refine ⟨41904145816232004679468319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27936097210821336452978879 41904145816232004679468319)
      ·
        refine ⟨62856218724348007019202479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41904145816232004679468319 62856218724348007019202479)
        ·
          refine ⟨94284328086522010528803719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62856218724348007019202479 94284328086522010528803719)
          ·
            refine ⟨141426492129783015793205579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94284328086522010528803719 141426492129783015793205579)
            ·
              refine ⟨212139738194674523689808369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141426492129783015793205579 212139738194674523689808369)
              ·
                refine ⟨159104803646005892767356277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212139738194674523689808369 159104803646005892767356277)
                ·
                  refine ⟨14916075341813052446939651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 159104803646005892767356277 14916075341813052446939651)
                  ·
                    refine ⟨22374113012719578670409477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14916075341813052446939651 22374113012719578670409477)
                    ·
                      refine ⟨4195146189884921000701777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22374113012719578670409477 4195146189884921000701777)
                      ·
                        rfl

theorem cell23_8170018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_8170018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8170018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8170018 prefixEnd_8170018 := by exact prefixLift 8170018
  have htrace : WordTrace (prefixWord ++ tailWord_8170018) baseStart_8170018 baseEnd_8170018 := by
    simpa [prefixWord, tailWord_8170018, baseEnd_8170018] using wordTrace_append hprefix tailTrace_8170018
  have hstable : (prefixWord ++ tailWord_8170018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8170018).length < 2 ^ (prefixWord ++ tailWord_8170018).sum := by decide
  have hdescent : baseEnd_8170018 < baseStart_8170018 := by decide
  rcases family_descends (prefixWord ++ tailWord_8170018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8170036 : List Nat := [2, 5, 1, 3, 2, 1, 2, 1, 6]
def baseStart_8170036 : Nat := 118140960795 + 8170036 * 2 ^ 59
def prefixEnd_8170036 : Nat := 4983230072969 + 3 ^ 40 * 8170036 * 2
def baseEnd_8170036 : Nat := 466128381392966881141855

theorem tailTrace_8170036 : CollatzResearch.WordTrace tailWord_8170036 prefixEnd_8170036 466128381392966881141855 := by
  unfold tailWord_8170036
  simp only [CollatzResearch.WordTrace]
  refine ⟨148992846714681188952964981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198657128952908251937286641 148992846714681188952964981)
  ·
    refine ⟨13968079379501361464340467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148992846714681188952964981 13968079379501361464340467)
    ·
      refine ⟨20952119069252042196510701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13968079379501361464340467 20952119069252042196510701)
      ·
        refine ⟨7857044650969515823691513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20952119069252042196510701 7857044650969515823691513)
        ·
          refine ⟨5892783488227136867768635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7857044650969515823691513 5892783488227136867768635)
          ·
            refine ⟨8839175232340705301652953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5892783488227136867768635 8839175232340705301652953)
            ·
              refine ⟨6629381424255528976239715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8839175232340705301652953 6629381424255528976239715)
              ·
                refine ⟨9944072136383293464359573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6629381424255528976239715 9944072136383293464359573)
                ·
                  refine ⟨466128381392966881141855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9944072136383293464359573 466128381392966881141855)
                  ·
                    rfl

theorem cell23_8170036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_8170036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8170036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8170036 prefixEnd_8170036 := by exact prefixLift 8170036
  have htrace : WordTrace (prefixWord ++ tailWord_8170036) baseStart_8170036 baseEnd_8170036 := by
    simpa [prefixWord, tailWord_8170036, baseEnd_8170036] using wordTrace_append hprefix tailTrace_8170036
  have hstable : (prefixWord ++ tailWord_8170036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8170036).length < 2 ^ (prefixWord ++ tailWord_8170036).sum := by decide
  have hdescent : baseEnd_8170036 < baseStart_8170036 := by decide
  rcases family_descends (prefixWord ++ tailWord_8170036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8170055 : List Nat := [1, 1, 4, 1, 4, 2, 1, 1, 3, 2, 3]
def baseStart_8170055 : Nat := 118140960795 + 8170055 * 2 ^ 59
def prefixEnd_8170055 : Nat := 4983230072969 + 3 ^ 40 * 8170055 * 2
def baseEnd_8170055 : Nat := 4195165188669137355939107

theorem tailTrace_8170055 : CollatzResearch.WordTrace tailWord_8170055 prefixEnd_8170055 4195165188669137355939107 := by
  unfold tailWord_8170055
  simp only [CollatzResearch.WordTrace]
  refine ⟨297986386416293544150871619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198657590944195696100581079 297986386416293544150871619)
  ·
    refine ⟨446979579624440316226307429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297986386416293544150871619 446979579624440316226307429)
    ·
      refine ⟨83808671179582559292432643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 446979579624440316226307429 83808671179582559292432643)
      ·
        refine ⟨125713006769373838938648965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83808671179582559292432643 125713006769373838938648965)
        ·
          refine ⟨23571188769257594800996681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125713006769373838938648965 23571188769257594800996681)
          ·
            refine ⟨17678391576943196100747511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23571188769257594800996681 17678391576943196100747511)
            ·
              refine ⟨26517587365414794151121267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17678391576943196100747511 26517587365414794151121267)
              ·
                refine ⟨39776381048122191226681901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26517587365414794151121267 39776381048122191226681901)
                ·
                  refine ⟨14916142893045821710005713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39776381048122191226681901 14916142893045821710005713)
                  ·
                    refine ⟨11187107169784366282504285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14916142893045821710005713 11187107169784366282504285)
                    ·
                      refine ⟨4195165188669137355939107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11187107169784366282504285 4195165188669137355939107)
                      ·
                        rfl

theorem cell23_8170055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3, 2, 3].length) (baseStart_8170055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8170055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8170055 prefixEnd_8170055 := by exact prefixLift 8170055
  have htrace : WordTrace (prefixWord ++ tailWord_8170055) baseStart_8170055 baseEnd_8170055 := by
    simpa [prefixWord, tailWord_8170055, baseEnd_8170055] using wordTrace_append hprefix tailTrace_8170055
  have hstable : (prefixWord ++ tailWord_8170055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8170055).length < 2 ^ (prefixWord ++ tailWord_8170055).sum := by decide
  have hdescent : baseEnd_8170055 < baseStart_8170055 := by decide
  rcases family_descends (prefixWord ++ tailWord_8170055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8170095 : List Nat := [1, 1, 2, 1, 3, 2, 3, 2, 3, 3, 2]
def baseStart_8170095 : Nat := 118140960795 + 8170095 * 2 ^ 59
def prefixEnd_8170095 : Nat := 4983230072969 + 3 ^ 40 * 8170095 * 2
def baseEnd_8170095 : Nat := 4195185727895317199438923

theorem tailTrace_8170095 : CollatzResearch.WordTrace tailWord_8170095 prefixEnd_8170095 4195185727895317199438923 := by
  unfold tailWord_8170095
  simp only [CollatzResearch.WordTrace]
  refine ⟨297987845336148630982327739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198658563557432420654885159 297987845336148630982327739)
  ·
    refine ⟨446981768004222946473491609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297987845336148630982327739 446981768004222946473491609)
    ·
      refine ⟨335236326003167209855118707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446981768004222946473491609 335236326003167209855118707)
      ·
        refine ⟨502854489004750814782678061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335236326003167209855118707 502854489004750814782678061)
        ·
          refine ⟨188570433376781555543504273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 502854489004750814782678061 188570433376781555543504273)
          ·
            refine ⟨141427825032586166657628205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188570433376781555543504273 141427825032586166657628205)
            ·
              refine ⟨53035434387219812496610577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141427825032586166657628205 53035434387219812496610577)
              ·
                refine ⟨39776575790414859372457933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53035434387219812496610577 39776575790414859372457933)
                ·
                  refine ⟨14916215921405572264671725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39776575790414859372457933 14916215921405572264671725)
                  ·
                    refine ⟨5593580970527089599251897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14916215921405572264671725 5593580970527089599251897)
                    ·
                      refine ⟨4195185727895317199438923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5593580970527089599251897 4195185727895317199438923)
                      ·
                        rfl

theorem cell23_8170095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3, 3, 2].length) (baseStart_8170095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8170095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8170095 prefixEnd_8170095 := by exact prefixLift 8170095
  have htrace : WordTrace (prefixWord ++ tailWord_8170095) baseStart_8170095 baseEnd_8170095 := by
    simpa [prefixWord, tailWord_8170095, baseEnd_8170095] using wordTrace_append hprefix tailTrace_8170095
  have hstable : (prefixWord ++ tailWord_8170095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8170095).length < 2 ^ (prefixWord ++ tailWord_8170095).sum := by decide
  have hdescent : baseEnd_8170095 < baseStart_8170095 := by decide
  rcases family_descends (prefixWord ++ tailWord_8170095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8170165 : List Nat := [1, 3, 3, 3, 1, 1, 2, 2, 7]
def baseStart_8170165 : Nat := 118140960795 + 8170165 * 2 ^ 59
def prefixEnd_8170165 : Nat := 4983230072969 + 3 ^ 40 * 8170165 * 2
def baseEnd_8170165 : Nat := 466135741282347991729289

theorem tailTrace_8170165 : CollatzResearch.WordTrace tailWord_8170165 prefixEnd_8170165 466135741282347991729289 := by
  unfold tailWord_8170165
  simp only [CollatzResearch.WordTrace]
  refine ⟨297990398445895032937375949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198660265630596688624917299 297990398445895032937375949)
  ·
    refine ⟨111746399417210637351515981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297990398445895032937375949 111746399417210637351515981)
    ·
      refine ⟨41904899781453989006818493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111746399417210637351515981 41904899781453989006818493)
      ·
        refine ⟨15714337418045245877556935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41904899781453989006818493 15714337418045245877556935)
        ·
          refine ⟨23571506127067868816335403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15714337418045245877556935 23571506127067868816335403)
          ·
            refine ⟨35357259190601803224503105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23571506127067868816335403 35357259190601803224503105)
            ·
              refine ⟨26517944392951352418377329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35357259190601803224503105 26517944392951352418377329)
              ·
                refine ⟨19888458294713514313782997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26517944392951352418377329 19888458294713514313782997)
                ·
                  refine ⟨466135741282347991729289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19888458294713514313782997 466135741282347991729289)
                  ·
                    rfl

theorem cell23_8170165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 7].length) (baseStart_8170165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8170165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8170165 prefixEnd_8170165 := by exact prefixLift 8170165
  have htrace : WordTrace (prefixWord ++ tailWord_8170165) baseStart_8170165 baseEnd_8170165 := by
    simpa [prefixWord, tailWord_8170165, baseEnd_8170165] using wordTrace_append hprefix tailTrace_8170165
  have hstable : (prefixWord ++ tailWord_8170165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8170165).length < 2 ^ (prefixWord ++ tailWord_8170165).sum := by decide
  have hdescent : baseEnd_8170165 < baseStart_8170165 := by decide
  rcases family_descends (prefixWord ++ tailWord_8170165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8170225 : List Nat := [1, 2, 2, 2, 2, 2, 2, 1, 5, 4]
def baseStart_8170225 : Nat := 118140960795 + 8170225 * 2 ^ 59
def prefixEnd_8170225 : Nat := 4983230072969 + 3 ^ 40 * 8170225 * 2
def baseEnd_8170225 : Nat := 1398417493460133896937775

theorem tailTrace_8170225 : CollatzResearch.WordTrace tailWord_8170225 prefixEnd_8170225 1398417493460133896937775 := by
  unfold tailWord_8170225
  simp only [CollatzResearch.WordTrace]
  refine ⟨297992586825677663184560129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198661724550451775456373419 297992586825677663184560129)
  ·
    refine ⟨223494440119258247388420097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297992586825677663184560129 223494440119258247388420097)
    ·
      refine ⟨167620830089443685541315073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223494440119258247388420097 167620830089443685541315073)
      ·
        refine ⟨125715622567082764155986305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167620830089443685541315073 125715622567082764155986305)
        ·
          refine ⟨94286716925312073116989729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125715622567082764155986305 94286716925312073116989729)
          ·
            refine ⟨70715037693984054837742297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94286716925312073116989729 70715037693984054837742297)
            ·
              refine ⟨53036278270488041128306723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70715037693984054837742297 53036278270488041128306723)
              ·
                refine ⟨79554417405732061692460085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53036278270488041128306723 79554417405732061692460085)
                ·
                  refine ⟨7458226631787380783668133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79554417405732061692460085 7458226631787380783668133)
                  ·
                    refine ⟨1398417493460133896937775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7458226631787380783668133 1398417493460133896937775)
                    ·
                      rfl

theorem cell23_8170225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 5, 4].length) (baseStart_8170225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8170225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8170225 prefixEnd_8170225 := by exact prefixLift 8170225
  have htrace : WordTrace (prefixWord ++ tailWord_8170225) baseStart_8170225 baseEnd_8170225 := by
    simpa [prefixWord, tailWord_8170225, baseEnd_8170225] using wordTrace_append hprefix tailTrace_8170225
  have hstable : (prefixWord ++ tailWord_8170225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8170225).length < 2 ^ (prefixWord ++ tailWord_8170225).sum := by decide
  have hdescent : baseEnd_8170225 < baseStart_8170225 := by decide
  rcases family_descends (prefixWord ++ tailWord_8170225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8170255 : List Nat := [1, 1, 2, 1, 1, 1, 8, 2, 6]
def baseStart_8170255 : Nat := 118140960795 + 8170255 * 2 ^ 59
def prefixEnd_8170255 : Nat := 4983230072969 + 3 ^ 40 * 8170255 * 2
def baseEnd_8170255 : Nat := 466140876088892952604243

theorem tailTrace_8170255 : CollatzResearch.WordTrace tailWord_8170255 prefixEnd_8170255 466140876088892952604243 := by
  unfold tailWord_8170255
  simp only [CollatzResearch.WordTrace]
  refine ⟨297993681015568978308152219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198662454010379318872101479 297993681015568978308152219)
  ·
    refine ⟨446990521523353467462228329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297993681015568978308152219 446990521523353467462228329)
    ·
      refine ⟨335242891142515100596671247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446990521523353467462228329 335242891142515100596671247)
      ·
        refine ⟨502864336713772650895006871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335242891142515100596671247 502864336713772650895006871)
        ·
          refine ⟨754296505070658976342510307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502864336713772650895006871 754296505070658976342510307)
          ·
            refine ⟨1131444757605988464513765461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754296505070658976342510307 1131444757605988464513765461)
            ·
              refine ⟨13259118253195177318520689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1131444757605988464513765461 13259118253195177318520689)
              ·
                refine ⟨9944338689896382988890517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13259118253195177318520689 9944338689896382988890517)
                ·
                  refine ⟨466140876088892952604243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9944338689896382988890517 466140876088892952604243)
                  ·
                    rfl

theorem cell23_8170255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2, 6].length) (baseStart_8170255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8170255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8170255 prefixEnd_8170255 := by exact prefixLift 8170255
  have htrace : WordTrace (prefixWord ++ tailWord_8170255) baseStart_8170255 baseEnd_8170255 := by
    simpa [prefixWord, tailWord_8170255, baseEnd_8170255] using wordTrace_append hprefix tailTrace_8170255
  have hstable : (prefixWord ++ tailWord_8170255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8170255).length < 2 ^ (prefixWord ++ tailWord_8170255).sum := by decide
  have hdescent : baseEnd_8170255 < baseStart_8170255 := by decide
  rcases family_descends (prefixWord ++ tailWord_8170255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8170286 : List Nat := [4, 1, 3, 2, 1, 3, 1, 1, 2, 2, 3]
def baseStart_8170286 : Nat := 118140960795 + 8170286 * 2 ^ 59
def prefixEnd_8170286 : Nat := 4983230072969 + 3 ^ 40 * 8170286 * 2
def baseEnd_8170286 : Nat := 4195283802700325952150545

theorem tailTrace_8170286 : CollatzResearch.WordTrace tailWord_8170286 prefixEnd_8170286 4195283802700325952150545 := by
  unfold tailWord_8170286
  simp only [CollatzResearch.WordTrace]
  refine ⟨37249351459807083825316339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198663207785637780401687141 37249351459807083825316339)
  ·
    refine ⟨55874027189710625737974509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37249351459807083825316339 55874027189710625737974509)
    ·
      refine ⟨20952760196141484651740441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55874027189710625737974509 20952760196141484651740441)
      ·
        refine ⟨15714570147106113488805331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20952760196141484651740441 15714570147106113488805331)
        ·
          refine ⟨23571855220659170233207997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15714570147106113488805331 23571855220659170233207997)
          ·
            refine ⟨8839445707747188837452999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23571855220659170233207997 8839445707747188837452999)
            ·
              refine ⟨13259168561620783256179499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8839445707747188837452999 13259168561620783256179499)
              ·
                refine ⟨19888752842431174884269249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13259168561620783256179499 19888752842431174884269249)
                ·
                  refine ⟨14916564631823381163201937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19888752842431174884269249 14916564631823381163201937)
                  ·
                    refine ⟨11187423473867535872401453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14916564631823381163201937 11187423473867535872401453)
                    ·
                      refine ⟨4195283802700325952150545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11187423473867535872401453 4195283802700325952150545)
                      ·
                        rfl

theorem cell23_8170286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_8170286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8170286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8170286 prefixEnd_8170286 := by exact prefixLift 8170286
  have htrace : WordTrace (prefixWord ++ tailWord_8170286) baseStart_8170286 baseEnd_8170286 := by
    simpa [prefixWord, tailWord_8170286, baseEnd_8170286] using wordTrace_append hprefix tailTrace_8170286
  have hstable : (prefixWord ++ tailWord_8170286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8170286).length < 2 ^ (prefixWord ++ tailWord_8170286).sum := by decide
  have hdescent : baseEnd_8170286 < baseStart_8170286 := by decide
  rcases family_descends (prefixWord ++ tailWord_8170286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8170316 : List Nat := [2, 2, 1, 3, 3, 1, 2, 4, 1, 1, 3]
def baseStart_8170316 : Nat := 118140960795 + 8170316 * 2 ^ 59
def prefixEnd_8170316 : Nat := 4983230072969 + 3 ^ 40 * 8170316 * 2
def baseEnd_8170316 : Nat := 4195299207119960834775407

theorem tailTrace_8170316 : CollatzResearch.WordTrace tailWord_8170316 prefixEnd_8170316 4195299207119960834775407 := by
  unfold tailWord_8170316
  simp only [CollatzResearch.WordTrace]
  refine ⟨148997952934173992863061401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198663937245565323817415201 148997952934173992863061401)
  ·
    refine ⟨111748464700630494647296051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148997952934173992863061401 111748464700630494647296051)
    ·
      refine ⟨167622697050945741970944077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111748464700630494647296051 167622697050945741970944077)
      ·
        refine ⟨62858511394104653239104029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167622697050945741970944077 62858511394104653239104029)
        ·
          refine ⟨23571941772789244964664011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62858511394104653239104029 23571941772789244964664011)
          ·
            refine ⟨35357912659183867446996017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23571941772789244964664011 35357912659183867446996017)
            ·
              refine ⟨26518434494387900585247013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35357912659183867446996017 26518434494387900585247013)
              ·
                refine ⟨4972206467697731359733815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26518434494387900585247013 4972206467697731359733815)
                ·
                  refine ⟨7458309701546597039600723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4972206467697731359733815 7458309701546597039600723)
                  ·
                    refine ⟨11187464552319895559401085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7458309701546597039600723 11187464552319895559401085)
                    ·
                      refine ⟨4195299207119960834775407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11187464552319895559401085 4195299207119960834775407)
                      ·
                        rfl

theorem cell23_8170316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 4, 1, 1, 3].length) (baseStart_8170316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8170316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8170316 prefixEnd_8170316 := by exact prefixLift 8170316
  have htrace : WordTrace (prefixWord ++ tailWord_8170316) baseStart_8170316 baseEnd_8170316 := by
    simpa [prefixWord, tailWord_8170316, baseEnd_8170316] using wordTrace_append hprefix tailTrace_8170316
  have hstable : (prefixWord ++ tailWord_8170316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8170316).length < 2 ^ (prefixWord ++ tailWord_8170316).sum := by decide
  have hdescent : baseEnd_8170316 < baseStart_8170316 := by decide
  rcases family_descends (prefixWord ++ tailWord_8170316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8170335 : List Nat := [1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 6]
def baseStart_8170335 : Nat := 118140960795 + 8170335 * 2 ^ 59
def prefixEnd_8170335 : Nat := 4983230072969 + 3 ^ 40 * 8170335 * 2
def baseEnd_8170335 : Nat := 4195308963252396260437819

theorem tailTrace_8170335 : CollatzResearch.WordTrace tailWord_8170335 prefixEnd_8170335 4195308963252396260437819 := by
  unfold tailWord_8170335
  simp only [CollatzResearch.WordTrace]
  refine ⟨297996598855279151971064459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198664399236852767980709639 297996598855279151971064459)
  ·
    refine ⟨446994898282918727956596689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297996598855279151971064459 446994898282918727956596689)
    ·
      refine ⟨335246173712189045967447517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446994898282918727956596689 335246173712189045967447517)
      ·
        refine ⟨125717315142070892237792819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335246173712189045967447517 125717315142070892237792819)
        ·
          refine ⟨188575972713106338356689229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125717315142070892237792819 188575972713106338356689229)
          ·
            refine ⟨70715989767414876883758461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188575972713106338356689229 70715989767414876883758461)
            ·
              refine ⟨26518496162780578831409423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70715989767414876883758461 26518496162780578831409423)
              ·
                refine ⟨39777744244170868247114135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26518496162780578831409423 39777744244170868247114135)
                ·
                  refine ⟨59666616366256302370671203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39777744244170868247114135 59666616366256302370671203)
                  ·
                    refine ⟨89499924549384453556006805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59666616366256302370671203 89499924549384453556006805)
                    ·
                      refine ⟨4195308963252396260437819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89499924549384453556006805 4195308963252396260437819)
                      ·
                        rfl

theorem cell23_8170335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_8170335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8170335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8170335 prefixEnd_8170335 := by exact prefixLift 8170335
  have htrace : WordTrace (prefixWord ++ tailWord_8170335) baseStart_8170335 baseEnd_8170335 := by
    simpa [prefixWord, tailWord_8170335, baseEnd_8170335] using wordTrace_append hprefix tailTrace_8170335
  have hstable : (prefixWord ++ tailWord_8170335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8170335).length < 2 ^ (prefixWord ++ tailWord_8170335).sum := by decide
  have hdescent : baseEnd_8170335 < baseStart_8170335 := by decide
  rcases family_descends (prefixWord ++ tailWord_8170335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8170339 : List Nat := [1, 1, 1, 5, 3, 2, 2, 2, 1, 1, 4]
def baseStart_8170339 : Nat := 118140960795 + 8170339 * 2 ^ 59
def prefixEnd_8170339 : Nat := 4983230072969 + 3 ^ 40 * 8170339 * 2
def baseEnd_8170339 : Nat := 4195311017175014244787801

theorem tailTrace_8170339 : CollatzResearch.WordTrace tailWord_8170339 prefixEnd_8170339 4195311017175014244787801 := by
  unfold tailWord_8170339
  simp only [CollatzResearch.WordTrace]
  refine ⟨297996744747264660654210071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198664496498176440436140047 297996744747264660654210071)
  ·
    refine ⟨446995117120896990981315107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297996744747264660654210071 446995117120896990981315107)
    ·
      refine ⟨670492675681345486471972661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446995117120896990981315107 670492675681345486471972661)
      ·
        refine ⟨62858688345126139356747437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 670492675681345486471972661 62858688345126139356747437)
        ·
          refine ⟨23572008129422302258780289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62858688345126139356747437 23572008129422302258780289)
          ·
            refine ⟨17679006097066726694085217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23572008129422302258780289 17679006097066726694085217)
            ·
              refine ⟨13259254572800045020563913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17679006097066726694085217 13259254572800045020563913)
              ·
                refine ⟨9944440929600033765422935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13259254572800045020563913 9944440929600033765422935)
                ·
                  refine ⟨14916661394400050648134403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9944440929600033765422935 14916661394400050648134403)
                  ·
                    refine ⟨22374992091600075972201605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14916661394400050648134403 22374992091600075972201605)
                    ·
                      refine ⟨4195311017175014244787801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22374992091600075972201605 4195311017175014244787801)
                      ·
                        rfl

theorem cell23_8170339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_8170339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8170339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8170339 prefixEnd_8170339 := by exact prefixLift 8170339
  have htrace : WordTrace (prefixWord ++ tailWord_8170339) baseStart_8170339 baseEnd_8170339 := by
    simpa [prefixWord, tailWord_8170339, baseEnd_8170339] using wordTrace_append hprefix tailTrace_8170339
  have hstable : (prefixWord ++ tailWord_8170339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8170339).length < 2 ^ (prefixWord ++ tailWord_8170339).sum := by decide
  have hdescent : baseEnd_8170339 < baseStart_8170339 := by decide
  rcases family_descends (prefixWord ++ tailWord_8170339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8170350 : List Nat := [4, 1, 2, 3, 2, 2, 1, 3, 1, 1, 3]
def baseStart_8170350 : Nat := 118140960795 + 8170350 * 2 ^ 59
def prefixEnd_8170350 : Nat := 4983230072969 + 3 ^ 40 * 8170350 * 2
def baseEnd_8170350 : Nat := 4195316665462213701750251

theorem tailTrace_8170350 : CollatzResearch.WordTrace tailWord_8170350 prefixEnd_8170350 4195316665462213701750251 := by
  unfold tailWord_8170350
  simp only [CollatzResearch.WordTrace]
  refine ⟨37249643243778101191607563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198664763966816539688573669 37249643243778101191607563)
  ·
    refine ⟨55874464865667151787411345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37249643243778101191607563 55874464865667151787411345)
    ·
      refine ⟨41905848649250363840558509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55874464865667151787411345 41905848649250363840558509)
      ·
        refine ⟨15714693243468886440209441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41905848649250363840558509 15714693243468886440209441)
        ·
          refine ⟨11786019932601664830157081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15714693243468886440209441 11786019932601664830157081)
          ·
            refine ⟨8839514949451248622617811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11786019932601664830157081 8839514949451248622617811)
            ·
              refine ⟨13259272424176872933926717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8839514949451248622617811 13259272424176872933926717)
              ·
                refine ⟨4972227159066327350222519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13259272424176872933926717 4972227159066327350222519)
                ·
                  refine ⟨7458340738599491025333779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4972227159066327350222519 7458340738599491025333779)
                  ·
                    refine ⟨11187511107899236538000669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7458340738599491025333779 11187511107899236538000669)
                    ·
                      refine ⟨4195316665462213701750251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11187511107899236538000669 4195316665462213701750251)
                      ·
                        rfl

theorem cell23_8170350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_8170350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8170350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8170350 prefixEnd_8170350 := by exact prefixLift 8170350
  have htrace : WordTrace (prefixWord ++ tailWord_8170350) baseStart_8170350 baseEnd_8170350 := by
    simpa [prefixWord, tailWord_8170350, baseEnd_8170350] using wordTrace_append hprefix tailTrace_8170350
  have hstable : (prefixWord ++ tailWord_8170350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8170350).length < 2 ^ (prefixWord ++ tailWord_8170350).sum := by decide
  have hdescent : baseEnd_8170350 < baseStart_8170350 := by decide
  rcases family_descends (prefixWord ++ tailWord_8170350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8170390 : List Nat := [5, 3, 1, 1, 1, 3, 1, 2, 1, 1, 4]
def baseStart_8170390 : Nat := 118140960795 + 8170390 * 2 ^ 59
def prefixEnd_8170390 : Nat := 4983230072969 + 3 ^ 40 * 8170390 * 2
def baseEnd_8170390 : Nat := 4195337204688393545250067

theorem tailTrace_8170390 : CollatzResearch.WordTrace tailWord_8170390 prefixEnd_8170390 4195337204688393545250067 := by
  unfold tailWord_8170390
  simp only [CollatzResearch.WordTrace]
  refine ⟨18624912804379993522769789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198665736580053264242877749 18624912804379993522769789)
  ·
    refine ⟨6984342301642497571038671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18624912804379993522769789 6984342301642497571038671)
    ·
      refine ⟨10476513452463746356558007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6984342301642497571038671 10476513452463746356558007)
      ·
        refine ⟨15714770178695619534837011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10476513452463746356558007 15714770178695619534837011)
        ·
          refine ⟨23572155268043429302255517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15714770178695619534837011 23572155268043429302255517)
          ·
            refine ⟨8839558225516285988345819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23572155268043429302255517 8839558225516285988345819)
            ·
              refine ⟨13259337338274428982518729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8839558225516285988345819 13259337338274428982518729)
              ·
                refine ⟨9944503003705821736889047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13259337338274428982518729 9944503003705821736889047)
                ·
                  refine ⟨14916754505558732605333571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9944503003705821736889047 14916754505558732605333571)
                  ·
                    refine ⟨22375131758338098908000357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14916754505558732605333571 22375131758338098908000357)
                    ·
                      refine ⟨4195337204688393545250067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22375131758338098908000357 4195337204688393545250067)
                      ·
                        rfl

theorem cell23_8170390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_8170390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8170390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8170390 prefixEnd_8170390 := by exact prefixLift 8170390
  have htrace : WordTrace (prefixWord ++ tailWord_8170390) baseStart_8170390 baseEnd_8170390 := by
    simpa [prefixWord, tailWord_8170390, baseEnd_8170390] using wordTrace_append hprefix tailTrace_8170390
  have hstable : (prefixWord ++ tailWord_8170390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8170390).length < 2 ^ (prefixWord ++ tailWord_8170390).sum := by decide
  have hdescent : baseEnd_8170390 < baseStart_8170390 := by decide
  rcases family_descends (prefixWord ++ tailWord_8170390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8170405 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 6, 6]
def baseStart_8170405 : Nat := 118140960795 + 8170405 * 2 ^ 59
def prefixEnd_8170405 : Nat := 4983230072969 + 3 ^ 40 * 8170405 * 2
def baseEnd_8170405 : Nat := 1398448302299403662187499

theorem tailTrace_8170405 : CollatzResearch.WordTrace tailWord_8170405 prefixEnd_8170405 1398448302299403662187499 := by
  unfold tailWord_8170405
  simp only [CollatzResearch.WordTrace]
  refine ⟨297999151965025553926112669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198666101310017035950741779 297999151965025553926112669)
  ·
    refine ⟨111749681986884582722292251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297999151965025553926112669 111749681986884582722292251)
    ·
      refine ⟨167624522980326874083438377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111749681986884582722292251 167624522980326874083438377)
      ·
        refine ⟨125718392235245155562578783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167624522980326874083438377 125718392235245155562578783)
        ·
          refine ⟨188577588352867733343868175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125718392235245155562578783 188577588352867733343868175)
          ·
            refine ⟨282866382529301600015802263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188577588352867733343868175 282866382529301600015802263)
            ·
              refine ⟨424299573793952400023703395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282866382529301600015802263 424299573793952400023703395)
              ·
                refine ⟨636449360690928600035555093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 424299573793952400023703395 636449360690928600035555093)
                ·
                  refine ⟨29833563782387278126666645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 636449360690928600035555093 29833563782387278126666645)
                  ·
                    refine ⟨1398448302299403662187499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29833563782387278126666645 1398448302299403662187499)
                    ·
                      rfl

theorem cell23_8170405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 6].length) (baseStart_8170405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8170405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8170405 prefixEnd_8170405 := by exact prefixLift 8170405
  have htrace : WordTrace (prefixWord ++ tailWord_8170405) baseStart_8170405 baseEnd_8170405 := by
    simpa [prefixWord, tailWord_8170405, baseEnd_8170405] using wordTrace_append hprefix tailTrace_8170405
  have hstable : (prefixWord ++ tailWord_8170405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8170405).length < 2 ^ (prefixWord ++ tailWord_8170405).sum := by decide
  have hdescent : baseEnd_8170405 < baseStart_8170405 := by decide
  rcases family_descends (prefixWord ++ tailWord_8170405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8170415 : List Nat := [1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 5]
def baseStart_8170415 : Nat := 118140960795 + 8170415 * 2 ^ 59
def prefixEnd_8170415 : Nat := 4983230072969 + 3 ^ 40 * 8170415 * 2
def baseEnd_8170415 : Nat := 4195350041704755947437451

theorem tailTrace_8170415 : CollatzResearch.WordTrace tailWord_8170415 prefixEnd_8170415 4195350041704755947437451 := by
  unfold tailWord_8170415
  simp only [CollatzResearch.WordTrace]
  refine ⟨297999516694989325633976699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198666344463326217089317799 297999516694989325633976699)
  ·
    refine ⟨446999275042483988450965049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297999516694989325633976699 446999275042483988450965049)
    ·
      refine ⟨335249456281862991338223787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446999275042483988450965049 335249456281862991338223787)
      ·
        refine ⟨502874184422794487007335681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335249456281862991338223787 502874184422794487007335681)
        ·
          refine ⟨377155638317095865255501761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 502874184422794487007335681 377155638317095865255501761)
          ·
            refine ⟨282866728737821898941626321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377155638317095865255501761 282866728737821898941626321)
            ·
              refine ⟨212150046553366424206219741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282866728737821898941626321 212150046553366424206219741)
              ·
                refine ⟨79556267457512409077332403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212150046553366424206219741 79556267457512409077332403)
                ·
                  refine ⟨119334401186268613615998605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79556267457512409077332403 119334401186268613615998605)
                  ·
                    refine ⟨44750400444850730105999477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119334401186268613615998605 44750400444850730105999477)
                    ·
                      refine ⟨4195350041704755947437451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44750400444850730105999477 4195350041704755947437451)
                      ·
                        rfl

theorem cell23_8170415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 5].length) (baseStart_8170415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8170415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8170415 prefixEnd_8170415 := by exact prefixLift 8170415
  have htrace : WordTrace (prefixWord ++ tailWord_8170415) baseStart_8170415 baseEnd_8170415 := by
    simpa [prefixWord, tailWord_8170415, baseEnd_8170415] using wordTrace_append hprefix tailTrace_8170415
  have hstable : (prefixWord ++ tailWord_8170415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8170415).length < 2 ^ (prefixWord ++ tailWord_8170415).sum := by decide
  have hdescent : baseEnd_8170415 < baseStart_8170415 := by decide
  rcases family_descends (prefixWord ++ tailWord_8170415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8170432 : List Nat := [2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 3]
def baseStart_8170432 : Nat := 118140960795 + 8170432 * 2 ^ 59
def prefixEnd_8170432 : Nat := 4983230072969 + 3 ^ 40 * 8170432 * 2
def baseEnd_8170432 : Nat := 4195358770875882380924873

theorem tailTrace_8170432 : CollatzResearch.WordTrace tailWord_8170432 prefixEnd_8170432 4195358770875882380924873 := by
  unfold tailWord_8170432
  simp only [CollatzResearch.WordTrace]
  refine ⟨149000068367963868768672775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198666757823951825024897033 149000068367963868768672775)
  ·
    refine ⟨223500102551945803153009163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149000068367963868768672775 223500102551945803153009163)
    ·
      refine ⟨335250153827918704729513745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223500102551945803153009163 335250153827918704729513745)
      ·
        refine ⟨251437615370939028547135309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335250153827918704729513745 251437615370939028547135309)
        ·
          refine ⟨94289105764102135705175741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251437615370939028547135309 94289105764102135705175741)
          ·
            refine ⟨35358414661538300889440903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94289105764102135705175741 35358414661538300889440903)
            ·
              refine ⟨53037621992307451334161355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35358414661538300889440903 53037621992307451334161355)
              ·
                refine ⟨79556432988461177001242033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53037621992307451334161355 79556432988461177001242033)
                ·
                  refine ⟨59667324741345882750931525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79556432988461177001242033 59667324741345882750931525)
                  ·
                    refine ⟨11187623389002353015799661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59667324741345882750931525 11187623389002353015799661)
                    ·
                      refine ⟨4195358770875882380924873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11187623389002353015799661 4195358770875882380924873)
                      ·
                        rfl

theorem cell23_8170432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 3].length) (baseStart_8170432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8170432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8170432 prefixEnd_8170432 := by exact prefixLift 8170432
  have htrace : WordTrace (prefixWord ++ tailWord_8170432) baseStart_8170432 baseEnd_8170432 := by
    simpa [prefixWord, tailWord_8170432, baseEnd_8170432] using wordTrace_append hprefix tailTrace_8170432
  have hstable : (prefixWord ++ tailWord_8170432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8170432).length < 2 ^ (prefixWord ++ tailWord_8170432).sum := by decide
  have hdescent : baseEnd_8170432 < baseStart_8170432 := by decide
  rcases family_descends (prefixWord ++ tailWord_8170432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8170446 : List Nat := [4, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2]
def baseStart_8170446 : Nat := 118140960795 + 8170446 * 2 ^ 59
def prefixEnd_8170446 : Nat := 4983230072969 + 3 ^ 40 * 8170446 * 2
def baseEnd_8170446 : Nat := 4195365959605045326149809

theorem tailTrace_8170446 : CollatzResearch.WordTrace tailWord_8170446 prefixEnd_8170446 4195365959605045326149809 := by
  unfold tailWord_8170446
  simp only [CollatzResearch.WordTrace]
  refine ⟨37250080919734627241044399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198667098238584678618903461 37250080919734627241044399)
  ·
    refine ⟨55875121379601940861566599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37250080919734627241044399 55875121379601940861566599)
    ·
      refine ⟨83812682069402911292349899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55875121379601940861566599 83812682069402911292349899)
      ·
        refine ⟨125719023104104366938524849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83812682069402911292349899 125719023104104366938524849)
        ·
          refine ⟨94289267328078275203893637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125719023104104366938524849 94289267328078275203893637)
          ·
            refine ⟨17679237624014676600730057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94289267328078275203893637 17679237624014676600730057)
            ·
              refine ⟨13259428218011007450547543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17679237624014676600730057 13259428218011007450547543)
              ·
                refine ⟨19889142327016511175821315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13259428218011007450547543 19889142327016511175821315)
                ·
                  refine ⟨29833713490524766763731973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19889142327016511175821315 29833713490524766763731973)
                  ·
                    refine ⟨5593821279473393768199745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29833713490524766763731973 5593821279473393768199745)
                    ·
                      refine ⟨4195365959605045326149809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5593821279473393768199745 4195365959605045326149809)
                      ·
                        rfl

theorem cell23_8170446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2].length) (baseStart_8170446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8170446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8170446 prefixEnd_8170446 := by exact prefixLift 8170446
  have htrace : WordTrace (prefixWord ++ tailWord_8170446) baseStart_8170446 baseEnd_8170446 := by
    simpa [prefixWord, tailWord_8170446, baseEnd_8170446] using wordTrace_append hprefix tailTrace_8170446
  have hstable : (prefixWord ++ tailWord_8170446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8170446).length < 2 ^ (prefixWord ++ tailWord_8170446).sum := by decide
  have hdescent : baseEnd_8170446 < baseStart_8170446 := by decide
  rcases family_descends (prefixWord ++ tailWord_8170446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8170452 : List Nat := [2, 4, 1, 2, 1, 2, 1, 1, 9]
def baseStart_8170452 : Nat := 118140960795 + 8170452 * 2 ^ 59
def prefixEnd_8170452 : Nat := 4983230072969 + 3 ^ 40 * 8170452 * 2
def baseEnd_8170452 : Nat := 466152115609885811408309

theorem tailTrace_8170452 : CollatzResearch.WordTrace tailWord_8170452 prefixEnd_8170452 466152115609885811408309 := by
  unfold tailWord_8170452
  simp only [CollatzResearch.WordTrace]
  refine ⟨149000433097927640476536805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198667244130570187302049073 149000433097927640476536805)
  ·
    refine ⟨27937581205861432589350651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149000433097927640476536805 27937581205861432589350651)
    ·
      refine ⟨41906371808792148884025977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27937581205861432589350651 41906371808792148884025977)
      ·
        refine ⟨31429778856594111663019483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41906371808792148884025977 31429778856594111663019483)
        ·
          refine ⟨47144668284891167494529225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31429778856594111663019483 47144668284891167494529225)
          ·
            refine ⟨35358501213668375620896919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47144668284891167494529225 35358501213668375620896919)
            ·
              refine ⟨53037751820502563431345379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35358501213668375620896919 53037751820502563431345379)
              ·
                refine ⟨79556627730753845147018069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53037751820502563431345379 79556627730753845147018069)
                ·
                  refine ⟨466152115609885811408309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 79556627730753845147018069 466152115609885811408309)
                  ·
                    rfl

theorem cell23_8170452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_8170452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8170452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8170452 prefixEnd_8170452 := by exact prefixLift 8170452
  have htrace : WordTrace (prefixWord ++ tailWord_8170452) baseStart_8170452 baseEnd_8170452 := by
    simpa [prefixWord, tailWord_8170452, baseEnd_8170452] using wordTrace_append hprefix tailTrace_8170452
  have hstable : (prefixWord ++ tailWord_8170452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8170452).length < 2 ^ (prefixWord ++ tailWord_8170452).sum := by decide
  have hdescent : baseEnd_8170452 < baseStart_8170452 := by decide
  rcases family_descends (prefixWord ++ tailWord_8170452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8170486 : List Nat := [5, 1, 1, 1, 3, 1, 2, 4, 5]
def baseStart_8170486 : Nat := 118140960795 + 8170486 * 2 ^ 59
def prefixEnd_8170486 : Nat := 4983230072969 + 3 ^ 40 * 8170486 * 2
def baseEnd_8170486 : Nat := 466154055425691685516625

theorem tailTrace_8170486 : CollatzResearch.WordTrace tailWord_8170486 prefixEnd_8170486 466154055425691685516625 := by
  unfold tailWord_8170486
  simp only [CollatzResearch.WordTrace]
  refine ⟨18625131642358256547488207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198668070851821403173207541 18625131642358256547488207)
  ·
    refine ⟨27937697463537384821232311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18625131642358256547488207 27937697463537384821232311)
    ·
      refine ⟨41906546195306077231848467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27937697463537384821232311 41906546195306077231848467)
      ·
        refine ⟨62859819292959115847772701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41906546195306077231848467 62859819292959115847772701)
        ·
          refine ⟨23572432234859668442914763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62859819292959115847772701 23572432234859668442914763)
          ·
            refine ⟨35358648352289502664372145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23572432234859668442914763 35358648352289502664372145)
            ·
              refine ⟨26518986264217126998279109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35358648352289502664372145 26518986264217126998279109)
              ·
                refine ⟨4972309924540711312177333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26518986264217126998279109 4972309924540711312177333)
                ·
                  refine ⟨466154055425691685516625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4972309924540711312177333 466154055425691685516625)
                  ·
                    rfl

theorem cell23_8170486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_8170486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8170486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8170486 prefixEnd_8170486 := by exact prefixLift 8170486
  have htrace : WordTrace (prefixWord ++ tailWord_8170486) baseStart_8170486 baseEnd_8170486 := by
    simpa [prefixWord, tailWord_8170486, baseEnd_8170486] using wordTrace_append hprefix tailTrace_8170486
  have hstable : (prefixWord ++ tailWord_8170486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8170486).length < 2 ^ (prefixWord ++ tailWord_8170486).sum := by decide
  have hdescent : baseEnd_8170486 < baseStart_8170486 := by decide
  rcases family_descends (prefixWord ++ tailWord_8170486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8170519 : List Nat := [1, 1, 3, 5, 1, 1, 2, 1, 1, 3, 4]
def baseStart_8170519 : Nat := 118140960795 + 8170519 * 2 ^ 59
def prefixEnd_8170519 : Nat := 4983230072969 + 3 ^ 40 * 8170519 * 2
def baseEnd_8170519 : Nat := 4195403443692823540536973

theorem tailTrace_8170519 : CollatzResearch.WordTrace tailWord_8170519 prefixEnd_8170519 4195403443692823540536973 := by
  unfold tailWord_8170519
  simp only [CollatzResearch.WordTrace]
  refine ⟨298003309886612551395762611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198668873257741700930508407 298003309886612551395762611)
  ·
    refine ⟨447004964829918827093643917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298003309886612551395762611 447004964829918827093643917)
    ·
      refine ⟨167626861811219560160116469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 447004964829918827093643917 167626861811219560160116469)
      ·
        refine ⟨15715018294801833765010919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167626861811219560160116469 15715018294801833765010919)
        ·
          refine ⟨23572527442202750647516379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15715018294801833765010919 23572527442202750647516379)
          ·
            refine ⟨35358791163304125971274569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23572527442202750647516379 35358791163304125971274569)
            ·
              refine ⟨26519093372478094478455927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35358791163304125971274569 26519093372478094478455927)
              ·
                refine ⟨39778640058717141717683891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26519093372478094478455927 39778640058717141717683891)
                ·
                  refine ⟨59667960088075712576525837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39778640058717141717683891 59667960088075712576525837)
                  ·
                    refine ⟨22375485033028392216197189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59667960088075712576525837 22375485033028392216197189)
                    ·
                      refine ⟨4195403443692823540536973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22375485033028392216197189 4195403443692823540536973)
                      ·
                        rfl

theorem cell23_8170519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_8170519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8170519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8170519 prefixEnd_8170519 := by exact prefixLift 8170519
  have htrace : WordTrace (prefixWord ++ tailWord_8170519) baseStart_8170519 baseEnd_8170519 := by
    simpa [prefixWord, tailWord_8170519, baseEnd_8170519] using wordTrace_append hprefix tailTrace_8170519
  have hstable : (prefixWord ++ tailWord_8170519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8170519).length < 2 ^ (prefixWord ++ tailWord_8170519).sum := by decide
  have hdescent : baseEnd_8170519 < baseStart_8170519 := by decide
  rcases family_descends (prefixWord ++ tailWord_8170519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8170539 : List Nat := [1, 1, 1, 1, 2, 1, 7, 2, 2, 2, 3]
def baseStart_8170539 : Nat := 118140960795 + 8170539 * 2 ^ 59
def prefixEnd_8170539 : Nat := 4983230072969 + 3 ^ 40 * 8170539 * 2
def baseEnd_8170539 : Nat := 4195413713305913462286881

theorem tailTrace_8170539 : CollatzResearch.WordTrace tailWord_8170539 prefixEnd_8170539 4195413713305913462286881 := by
  unfold tailWord_8170539
  simp only [CollatzResearch.WordTrace]
  refine ⟨298004039346540094811490671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198669359564360063207660447 298004039346540094811490671)
  ·
    refine ⟨447006059019810142217236007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298004039346540094811490671 447006059019810142217236007)
    ·
      refine ⟨670509088529715213325854011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447006059019810142217236007 670509088529715213325854011)
      ·
        refine ⟨1005763632794572819988781017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 670509088529715213325854011 1005763632794572819988781017)
        ·
          refine ⟨754322724595929614991585763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1005763632794572819988781017 754322724595929614991585763)
          ·
            refine ⟨1131484086893894422487378645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754322724595929614991585763 1131484086893894422487378645)
            ·
              refine ⟨26519158286575650527047937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1131484086893894422487378645 26519158286575650527047937)
              ·
                refine ⟨19889368714931737895285953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26519158286575650527047937 19889368714931737895285953)
                ·
                  refine ⟨14917026536198803421464465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19889368714931737895285953 14917026536198803421464465)
                  ·
                    refine ⟨11187769902149102566098349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14917026536198803421464465 11187769902149102566098349)
                    ·
                      refine ⟨4195413713305913462286881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11187769902149102566098349 4195413713305913462286881)
                      ·
                        rfl

theorem cell23_8170539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2, 2, 3].length) (baseStart_8170539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8170539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8170539 prefixEnd_8170539 := by exact prefixLift 8170539
  have htrace : WordTrace (prefixWord ++ tailWord_8170539) baseStart_8170539 baseEnd_8170539 := by
    simpa [prefixWord, tailWord_8170539, baseEnd_8170539] using wordTrace_append hprefix tailTrace_8170539
  have hstable : (prefixWord ++ tailWord_8170539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8170539).length < 2 ^ (prefixWord ++ tailWord_8170539).sum := by decide
  have hdescent : baseEnd_8170539 < baseStart_8170539 := by decide
  rcases family_descends (prefixWord ++ tailWord_8170539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8170573 : List Nat := [1, 6, 1, 1, 1, 3, 2, 1, 2, 2, 3]
def baseStart_8170573 : Nat := 118140960795 + 8170573 * 2 ^ 59
def prefixEnd_8170573 : Nat := 4983230072969 + 3 ^ 40 * 8170573 * 2
def baseEnd_8170573 : Nat := 4195431171648166329261725

theorem tailTrace_8170573 : CollatzResearch.WordTrace tailWord_8170573 prefixEnd_8170573 4195431171648166329261725 := by
  unfold tailWord_8170573
  simp only [CollatzResearch.WordTrace]
  refine ⟨298005279428416918618228373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198670186285611279078818915 298005279428416918618228373)
  ·
    refine ⟨13968997473207043060229455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 298005279428416918618228373 13968997473207043060229455)
    ·
      refine ⟨20953496209810564590344183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13968997473207043060229455 20953496209810564590344183)
      ·
        refine ⟨31430244314715846885516275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20953496209810564590344183 31430244314715846885516275)
        ·
          refine ⟨47145366472073770328274413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31430244314715846885516275 47145366472073770328274413)
          ·
            refine ⟨17679512427027663873102905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47145366472073770328274413 17679512427027663873102905)
            ·
              refine ⟨13259634320270747904827179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17679512427027663873102905 13259634320270747904827179)
              ·
                refine ⟨19889451480406121857240769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13259634320270747904827179 19889451480406121857240769)
                ·
                  refine ⟨14917088610304591392930577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19889451480406121857240769 14917088610304591392930577)
                  ·
                    refine ⟨11187816457728443544697933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14917088610304591392930577 11187816457728443544697933)
                    ·
                      refine ⟨4195431171648166329261725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11187816457728443544697933 4195431171648166329261725)
                      ·
                        rfl

theorem cell23_8170573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_8170573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8170573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8170573 prefixEnd_8170573 := by exact prefixLift 8170573
  have htrace : WordTrace (prefixWord ++ tailWord_8170573) baseStart_8170573 baseEnd_8170573 := by
    simpa [prefixWord, tailWord_8170573, baseEnd_8170573] using wordTrace_append hprefix tailTrace_8170573
  have hstable : (prefixWord ++ tailWord_8170573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8170573).length < 2 ^ (prefixWord ++ tailWord_8170573).sum := by decide
  have hdescent : baseEnd_8170573 < baseStart_8170573 := by decide
  rcases family_descends (prefixWord ++ tailWord_8170573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8170590 : List Nat := [4, 4, 1, 1, 1, 1, 2, 2, 2, 2, 3]
def baseStart_8170590 : Nat := 118140960795 + 8170590 * 2 ^ 59
def prefixEnd_8170590 : Nat := 4983230072969 + 3 ^ 40 * 8170590 * 2
def baseEnd_8170590 : Nat := 4195439900819292762749147

theorem tailTrace_8170590 : CollatzResearch.WordTrace tailWord_8170590 prefixEnd_8170590 4195439900819292762749147 := by
  unfold tailWord_8170590
  simp only [CollatzResearch.WordTrace]
  refine ⟨37250737433669416315199653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198670599646236887014398149 37250737433669416315199653)
  ·
    refine ⟨6984513268813015559099935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37250737433669416315199653 6984513268813015559099935)
    ·
      refine ⟨10476769903219523338649903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6984513268813015559099935 10476769903219523338649903)
      ·
        refine ⟨15715154854829285007974855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10476769903219523338649903 15715154854829285007974855)
        ·
          refine ⟨23572732282243927511962283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15715154854829285007974855 23572732282243927511962283)
          ·
            refine ⟨35359098423365891267943425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23572732282243927511962283 35359098423365891267943425)
            ·
              refine ⟨26519323817524418450957569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35359098423365891267943425 26519323817524418450957569)
              ·
                refine ⟨19889492863143313838218177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26519323817524418450957569 19889492863143313838218177)
                ·
                  refine ⟨14917119647357485378663633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19889492863143313838218177 14917119647357485378663633)
                  ·
                    refine ⟨11187839735518114033997725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14917119647357485378663633 11187839735518114033997725)
                    ·
                      refine ⟨4195439900819292762749147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11187839735518114033997725 4195439900819292762749147)
                      ·
                        rfl

theorem cell23_8170590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_8170590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8170590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8170590 prefixEnd_8170590 := by exact prefixLift 8170590
  have htrace : WordTrace (prefixWord ++ tailWord_8170590) baseStart_8170590 baseEnd_8170590 := by
    simpa [prefixWord, tailWord_8170590, baseEnd_8170590] using wordTrace_append hprefix tailTrace_8170590
  have hstable : (prefixWord ++ tailWord_8170590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8170590).length < 2 ^ (prefixWord ++ tailWord_8170590).sum := by decide
  have hdescent : baseEnd_8170590 < baseStart_8170590 := by decide
  rcases family_descends (prefixWord ++ tailWord_8170590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8170659 : List Nat := [1, 1, 1, 4, 1, 1, 1, 4, 3, 3, 3]
def baseStart_8170659 : Nat := 118140960795 + 8170659 * 2 ^ 59
def prefixEnd_8170659 : Nat := 4983230072969 + 3 ^ 40 * 8170659 * 2
def baseEnd_8170659 : Nat := 4195475330984452992786329

theorem tailTrace_8170659 : CollatzResearch.WordTrace tailWord_8170659 prefixEnd_8170659 4195475330984452992786329 := by
  unfold tailWord_8170659
  simp only [CollatzResearch.WordTrace]
  refine ⟨298008416106105355305859031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198672277404070236870572687 298008416106105355305859031)
  ·
    refine ⟨447012624159158032958788547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298008416106105355305859031 447012624159158032958788547)
    ·
      refine ⟨670518936238737049438182821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447012624159158032958788547 670518936238737049438182821)
      ·
        refine ⟨125722300544763196769659279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 670518936238737049438182821 125722300544763196769659279)
        ·
          refine ⟨188583450817144795154488919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125722300544763196769659279 188583450817144795154488919)
          ·
            refine ⟨282875176225717192731733379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188583450817144795154488919 282875176225717192731733379)
            ·
              refine ⟨424312764338575789097600069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282875176225717192731733379 424312764338575789097600069)
              ·
                refine ⟨79558643313482960455800013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 424312764338575789097600069 79558643313482960455800013)
                ·
                  refine ⟨29834491242556110170925005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79558643313482960455800013 29834491242556110170925005)
                  ·
                    refine ⟨11187934215958541314096877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29834491242556110170925005 11187934215958541314096877)
                    ·
                      refine ⟨4195475330984452992786329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11187934215958541314096877 4195475330984452992786329)
                      ·
                        rfl

theorem cell23_8170659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 3, 3].length) (baseStart_8170659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8170659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8170659 prefixEnd_8170659 := by exact prefixLift 8170659
  have htrace : WordTrace (prefixWord ++ tailWord_8170659) baseStart_8170659 baseEnd_8170659 := by
    simpa [prefixWord, tailWord_8170659, baseEnd_8170659] using wordTrace_append hprefix tailTrace_8170659
  have hstable : (prefixWord ++ tailWord_8170659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8170659).length < 2 ^ (prefixWord ++ tailWord_8170659).sum := by decide
  have hdescent : baseEnd_8170659 < baseStart_8170659 := by decide
  rcases family_descends (prefixWord ++ tailWord_8170659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8170660 : List Nat := [2, 3, 1, 2, 3, 2, 2, 1, 3, 2, 2]
def baseStart_8170660 : Nat := 118140960795 + 8170660 * 2 ^ 59
def prefixEnd_8170660 : Nat := 4983230072969 + 3 ^ 40 * 8170660 * 2
def baseEnd_8170660 : Nat := 4195475844465107488873825

theorem tailTrace_8170660 : CollatzResearch.WordTrace tailWord_8170660 prefixEnd_8170660 4195475844465107488873825 := by
  unfold tailWord_8170660
  simp only [CollatzResearch.WordTrace]
  refine ⟨149004226289550866238322717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198672301719401154984430289 149004226289550866238322717)
  ·
    refine ⟨55876584858581574839371019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149004226289550866238322717 55876584858581574839371019)
    ·
      refine ⟨83814877287872362259056529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55876584858581574839371019 83814877287872362259056529)
      ·
        refine ⟨62861157965904271694292397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83814877287872362259056529 62861157965904271694292397)
        ·
          refine ⟨23572934237214101885359649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62861157965904271694292397 23572934237214101885359649)
          ·
            refine ⟨17679700677910576414019737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23572934237214101885359649 17679700677910576414019737)
            ·
              refine ⟨13259775508432932310514803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17679700677910576414019737 13259775508432932310514803)
              ·
                refine ⟨19889663262649398465772205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13259775508432932310514803 19889663262649398465772205)
                ·
                  refine ⟨7458623723493524424664577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19889663262649398465772205 7458623723493524424664577)
                  ·
                    refine ⟨5593967792620143318498433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7458623723493524424664577 5593967792620143318498433)
                    ·
                      refine ⟨4195475844465107488873825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5593967792620143318498433 4195475844465107488873825)
                      ·
                        rfl

theorem cell23_8170660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 3, 2, 2].length) (baseStart_8170660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8170660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8170660 prefixEnd_8170660 := by exact prefixLift 8170660
  have htrace : WordTrace (prefixWord ++ tailWord_8170660) baseStart_8170660 baseEnd_8170660 := by
    simpa [prefixWord, tailWord_8170660, baseEnd_8170660] using wordTrace_append hprefix tailTrace_8170660
  have hstable : (prefixWord ++ tailWord_8170660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8170660).length < 2 ^ (prefixWord ++ tailWord_8170660).sum := by decide
  have hdescent : baseEnd_8170660 < baseStart_8170660 := by decide
  rcases family_descends (prefixWord ++ tailWord_8170660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8170673 : List Nat := [1, 2, 2, 5, 1, 3, 1, 1, 1, 2, 4]
def baseStart_8170673 : Nat := 118140960795 + 8170673 * 2 ^ 59
def prefixEnd_8170673 : Nat := 4983230072969 + 3 ^ 40 * 8170673 * 2
def baseEnd_8170673 : Nat := 4195482519713615938011265

theorem tailTrace_8170673 : CollatzResearch.WordTrace tailWord_8170673 prefixEnd_8170673 4195482519713615938011265 := by
  unfold tailWord_8170673
  simp only [CollatzResearch.WordTrace]
  refine ⟨298008926728054635696868673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198672617818703090464579115 298008926728054635696868673)
  ·
    refine ⟨223506695046040976772651505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298008926728054635696868673 223506695046040976772651505)
    ·
      refine ⟨167630021284530732579488629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223506695046040976772651505 167630021284530732579488629)
      ·
        refine ⟨15715314495424756179327059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167630021284530732579488629 15715314495424756179327059)
        ·
          refine ⟨23572971743137134268990589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15715314495424756179327059 23572971743137134268990589)
          ·
            refine ⟨8839864403676425350871471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23572971743137134268990589 8839864403676425350871471)
            ·
              refine ⟨13259796605514638026307207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8839864403676425350871471 13259796605514638026307207)
              ·
                refine ⟨19889694908271957039460811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13259796605514638026307207 19889694908271957039460811)
                ·
                  refine ⟨29834542362407935559191217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19889694908271957039460811 29834542362407935559191217)
                  ·
                    refine ⟨22375906771805951669393413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29834542362407935559191217 22375906771805951669393413)
                    ·
                      refine ⟨4195482519713615938011265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22375906771805951669393413 4195482519713615938011265)
                      ·
                        rfl

theorem cell23_8170673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_8170673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8170673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8170673 prefixEnd_8170673 := by exact prefixLift 8170673
  have htrace : WordTrace (prefixWord ++ tailWord_8170673) baseStart_8170673 baseEnd_8170673 := by
    simpa [prefixWord, tailWord_8170673, baseEnd_8170673] using wordTrace_append hprefix tailTrace_8170673
  have hstable : (prefixWord ++ tailWord_8170673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8170673).length < 2 ^ (prefixWord ++ tailWord_8170673).sum := by decide
  have hdescent : baseEnd_8170673 < baseStart_8170673 := by decide
  rcases family_descends (prefixWord ++ tailWord_8170673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8170750 : List Nat := [4, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2]
def baseStart_8170750 : Nat := 118140960795 + 8170750 * 2 ^ 59
def prefixEnd_8170750 : Nat := 4983230072969 + 3 ^ 40 * 8170750 * 2
def baseEnd_8170750 : Nat := 4195522057724012136748411

theorem tailTrace_8170750 : CollatzResearch.WordTrace tailWord_8170750 prefixEnd_8170750 4195522057724012136748411 := by
  unfold tailWord_8170750
  simp only [CollatzResearch.WordTrace]
  refine ⟨37251466893596959730927713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198674490099183785231614469 37251466893596959730927713)
  ·
    refine ⟨27938600170197719798195785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37251466893596959730927713 27938600170197719798195785)
    ·
      refine ⟨20953950127648289848646839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27938600170197719798195785 20953950127648289848646839)
      ·
        refine ⟨31430925191472434772970259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20953950127648289848646839 31430925191472434772970259)
        ·
          refine ⟨47146387787208652159455389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31430925191472434772970259 47146387787208652159455389)
          ·
            refine ⟨17679895420203244559795771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47146387787208652159455389 17679895420203244559795771)
            ·
              refine ⟨26519843130304866839693657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17679895420203244559795771 26519843130304866839693657)
              ·
                refine ⟨19889882347728650129770243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26519843130304866839693657 19889882347728650129770243)
                ·
                  refine ⟨29834823521592975194655365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19889882347728650129770243 29834823521592975194655365)
                  ·
                    refine ⟨5594029410298682848997881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29834823521592975194655365 5594029410298682848997881)
                    ·
                      refine ⟨4195522057724012136748411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5594029410298682848997881 4195522057724012136748411)
                      ·
                        rfl

theorem cell23_8170750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_8170750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8170750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8170750 prefixEnd_8170750 := by exact prefixLift 8170750
  have htrace : WordTrace (prefixWord ++ tailWord_8170750) baseStart_8170750 baseEnd_8170750 := by
    simpa [prefixWord, tailWord_8170750, baseEnd_8170750] using wordTrace_append hprefix tailTrace_8170750
  have hstable : (prefixWord ++ tailWord_8170750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8170750).length < 2 ^ (prefixWord ++ tailWord_8170750).sum := by decide
  have hdescent : baseEnd_8170750 < baseStart_8170750 := by decide
  rcases family_descends (prefixWord ++ tailWord_8170750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8170754 : List Nat := [3, 4, 1, 1, 3, 1, 3, 1, 1, 3, 2]
def baseStart_8170754 : Nat := 118140960795 + 8170754 * 2 ^ 59
def prefixEnd_8170754 : Nat := 4983230072969 + 3 ^ 40 * 8170754 * 2
def baseEnd_8170754 : Nat := 4195524111646630121098393

theorem tailTrace_8170754 : CollatzResearch.WordTrace tailWord_8170754 prefixEnd_8170754 4195524111646630121098393 := by
  unfold tailWord_8170754
  simp only [CollatzResearch.WordTrace]
  refine ⟨74502970260190296632641829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198674587360507457687044877 74502970260190296632641829)
  ·
    refine ⟨13969306923785680618620343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74502970260190296632641829 13969306923785680618620343)
    ·
      refine ⟨20953960385678520927930515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13969306923785680618620343 20953960385678520927930515)
      ·
        refine ⟨31430940578517781391895773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20953960385678520927930515 31430940578517781391895773)
        ·
          refine ⟨11786602716944168021960915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31430940578517781391895773 11786602716944168021960915)
          ·
            refine ⟨17679904075416252032941373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11786602716944168021960915 17679904075416252032941373)
            ·
              refine ⟨6629964028281094512353015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17679904075416252032941373 6629964028281094512353015)
              ·
                refine ⟨9944946042421641768529523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6629964028281094512353015 9944946042421641768529523)
                ·
                  refine ⟨14917419063632462652794285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9944946042421641768529523 14917419063632462652794285)
                  ·
                    refine ⟨5594032148862173494797857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14917419063632462652794285 5594032148862173494797857)
                    ·
                      refine ⟨4195524111646630121098393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5594032148862173494797857 4195524111646630121098393)
                      ·
                        rfl

theorem cell23_8170754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_8170754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8170754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8170754 prefixEnd_8170754 := by exact prefixLift 8170754
  have htrace : WordTrace (prefixWord ++ tailWord_8170754) baseStart_8170754 baseEnd_8170754 := by
    simpa [prefixWord, tailWord_8170754, baseEnd_8170754] using wordTrace_append hprefix tailTrace_8170754
  have hstable : (prefixWord ++ tailWord_8170754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8170754).length < 2 ^ (prefixWord ++ tailWord_8170754).sum := by decide
  have hdescent : baseEnd_8170754 < baseStart_8170754 := by decide
  rcases family_descends (prefixWord ++ tailWord_8170754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8170783 : List Nat := [1, 1, 2, 4, 4, 1, 1, 1, 2, 3, 3]
def baseStart_8170783 : Nat := 118140960795 + 8170783 * 2 ^ 59
def prefixEnd_8170783 : Nat := 4983230072969 + 3 ^ 40 * 8170783 * 2
def baseEnd_8170783 : Nat := 4195539002585610507635759

theorem tailTrace_8170783 : CollatzResearch.WordTrace tailWord_8170783 prefixEnd_8170783 4195539002585610507635759 := by
  unfold tailWord_8170783
  simp only [CollatzResearch.WordTrace]
  refine ⟨298012938757656124483373003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198675292505104082988915335 298012938757656124483373003)
  ·
    refine ⟨447019408136484186725059505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298012938757656124483373003 447019408136484186725059505)
    ·
      refine ⟨335264556102363140043794629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447019408136484186725059505 335264556102363140043794629)
      ·
        refine ⟨62862104269193088758211493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 335264556102363140043794629 62862104269193088758211493)
        ·
          refine ⟨11786644550473704142164655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62862104269193088758211493 11786644550473704142164655)
          ·
            refine ⟨17679966825710556213246983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11786644550473704142164655 17679966825710556213246983)
            ·
              refine ⟨26519950238565834319870475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17679966825710556213246983 26519950238565834319870475)
              ·
                refine ⟨39779925357848751479805713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26519950238565834319870475 39779925357848751479805713)
                ·
                  refine ⟨29834944018386563609854285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39779925357848751479805713 29834944018386563609854285)
                  ·
                    refine ⟨11188104006894961353695357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29834944018386563609854285 11188104006894961353695357)
                    ·
                      refine ⟨4195539002585610507635759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11188104006894961353695357 4195539002585610507635759)
                      ·
                        rfl

theorem cell23_8170783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_8170783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8170783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8170783 prefixEnd_8170783 := by exact prefixLift 8170783
  have htrace : WordTrace (prefixWord ++ tailWord_8170783) baseStart_8170783 baseEnd_8170783 := by
    simpa [prefixWord, tailWord_8170783, baseEnd_8170783] using wordTrace_append hprefix tailTrace_8170783
  have hstable : (prefixWord ++ tailWord_8170783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8170783).length < 2 ^ (prefixWord ++ tailWord_8170783).sum := by decide
  have hdescent : baseEnd_8170783 < baseStart_8170783 := by decide
  rcases family_descends (prefixWord ++ tailWord_8170783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8170803 : List Nat := [1, 1, 1, 2, 5, 4, 1, 1, 2, 5]
def baseStart_8170803 : Nat := 118140960795 + 8170803 * 2 ^ 59
def prefixEnd_8170803 : Nat := 4983230072969 + 3 ^ 40 * 8170803 * 2
def baseEnd_8170803 : Nat := 1398516424066233476461889

theorem tailTrace_8170803 : CollatzResearch.WordTrace tailWord_8170803 prefixEnd_8170803 1398516424066233476461889 := by
  unfold tailWord_8170803
  simp only [CollatzResearch.WordTrace]
  refine ⟨298013668217583667899101063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198675778811722445266067375 298013668217583667899101063)
  ·
    refine ⟨447020502326375501848651595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298013668217583667899101063 447020502326375501848651595)
    ·
      refine ⟨670530753489563252772977393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447020502326375501848651595 670530753489563252772977393)
      ·
        refine ⟨502898065117172439579733045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 670530753489563252772977393 502898065117172439579733045)
        ·
          refine ⟨47146693604734916210599973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 502898065117172439579733045 47146693604734916210599973)
          ·
            refine ⟨8840005050887796789487495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47146693604734916210599973 8840005050887796789487495)
            ·
              refine ⟨13260007576331695184231243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8840005050887796789487495 13260007576331695184231243)
              ·
                refine ⟨19890011364497542776346865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13260007576331695184231243 19890011364497542776346865)
                ·
                  refine ⟨14917508523373157082260149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19890011364497542776346865 14917508523373157082260149)
                  ·
                    refine ⟨1398516424066233476461889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14917508523373157082260149 1398516424066233476461889)
                    ·
                      rfl

theorem cell23_8170803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 2, 5].length) (baseStart_8170803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8170803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8170803 prefixEnd_8170803 := by exact prefixLift 8170803
  have htrace : WordTrace (prefixWord ++ tailWord_8170803) baseStart_8170803 baseEnd_8170803 := by
    simpa [prefixWord, tailWord_8170803, baseEnd_8170803] using wordTrace_append hprefix tailTrace_8170803
  have hstable : (prefixWord ++ tailWord_8170803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8170803).length < 2 ^ (prefixWord ++ tailWord_8170803).sum := by decide
  have hdescent : baseEnd_8170803 < baseStart_8170803 := by decide
  rcases family_descends (prefixWord ++ tailWord_8170803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8170816 : List Nat := [2, 1, 1, 2, 2, 1, 3, 2, 5, 4]
def baseStart_8170816 : Nat := 118140960795 + 8170816 * 2 ^ 59
def prefixEnd_8170816 : Nat := 4983230072969 + 3 ^ 40 * 8170816 * 2
def baseEnd_8170816 : Nat := 1398518649149069626174369

theorem tailTrace_8170816 : CollatzResearch.WordTrace tailWord_8170816 prefixEnd_8170816 1398518649149069626174369 := by
  unfold tailWord_8170816
  simp only [CollatzResearch.WordTrace]
  refine ⟨149007071183268285559662151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198676094911024380746216201 149007071183268285559662151)
  ·
    refine ⟨223510606774902428339493227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149007071183268285559662151 223510606774902428339493227)
    ·
      refine ⟨335265910162353642509239841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223510606774902428339493227 335265910162353642509239841)
      ·
        refine ⟨251449432621765231881929881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335265910162353642509239841 251449432621765231881929881)
        ·
          refine ⟨188587074466323923911447411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251449432621765231881929881 188587074466323923911447411)
          ·
            refine ⟨282880611699485885867171117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188587074466323923911447411 282880611699485885867171117)
            ·
              refine ⟨106080229387307207200189169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 282880611699485885867171117 106080229387307207200189169)
              ·
                refine ⟨79560172040480405400141877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106080229387307207200189169 79560172040480405400141877)
                ·
                  refine ⟨7458766128795038006263301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79560172040480405400141877 7458766128795038006263301)
                  ·
                    refine ⟨1398518649149069626174369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7458766128795038006263301 1398518649149069626174369)
                    ·
                      rfl

theorem cell23_8170816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 5, 4].length) (baseStart_8170816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8170816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8170816 prefixEnd_8170816 := by exact prefixLift 8170816
  have htrace : WordTrace (prefixWord ++ tailWord_8170816) baseStart_8170816 baseEnd_8170816 := by
    simpa [prefixWord, tailWord_8170816, baseEnd_8170816] using wordTrace_append hprefix tailTrace_8170816
  have hstable : (prefixWord ++ tailWord_8170816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8170816).length < 2 ^ (prefixWord ++ tailWord_8170816).sum := by decide
  have hdescent : baseEnd_8170816 < baseStart_8170816 := by decide
  rcases family_descends (prefixWord ++ tailWord_8170816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8170823 : List Nat := [1, 1, 4, 1, 2, 3, 1, 2, 2, 4, 2]
def baseStart_8170823 : Nat := 118140960795 + 8170823 * 2 ^ 59
def prefixEnd_8170823 : Nat := 4983230072969 + 3 ^ 40 * 8170823 * 2
def baseEnd_8170823 : Nat := 4195559541811790351135575

theorem tailTrace_8170823 : CollatzResearch.WordTrace tailWord_8170823 prefixEnd_8170823 4195559541811790351135575 := by
  unfold tailWord_8170823
  simp only [CollatzResearch.WordTrace]
  refine ⟨298014397677511211314829123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198676265118340807543219415 298014397677511211314829123)
  ·
    refine ⟨447021596516266816972243685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298014397677511211314829123 447021596516266816972243685)
    ·
      refine ⟨83816549346800028182295691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 447021596516266816972243685 83816549346800028182295691)
      ·
        refine ⟨125724824020200042273443537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83816549346800028182295691 125724824020200042273443537)
        ·
          refine ⟨94293618015150031705082653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125724824020200042273443537 94293618015150031705082653)
          ·
            refine ⟨35360106755681261889405995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94293618015150031705082653 35360106755681261889405995)
            ·
              refine ⟨53040160133521892834108993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35360106755681261889405995 53040160133521892834108993)
              ·
                refine ⟨39780120100141419625581745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53040160133521892834108993 39780120100141419625581745)
                ·
                  refine ⟨29835090075106064719186309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39780120100141419625581745 29835090075106064719186309)
                  ·
                    refine ⟨5594079389082387134847433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29835090075106064719186309 5594079389082387134847433)
                    ·
                      refine ⟨4195559541811790351135575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5594079389082387134847433 4195559541811790351135575)
                      ·
                        rfl

theorem cell23_8170823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 4, 2].length) (baseStart_8170823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8170823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8170823 prefixEnd_8170823 := by exact prefixLift 8170823
  have htrace : WordTrace (prefixWord ++ tailWord_8170823) baseStart_8170823 baseEnd_8170823 := by
    simpa [prefixWord, tailWord_8170823, baseEnd_8170823] using wordTrace_append hprefix tailTrace_8170823
  have hstable : (prefixWord ++ tailWord_8170823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8170823).length < 2 ^ (prefixWord ++ tailWord_8170823).sum := by decide
  have hdescent : baseEnd_8170823 < baseStart_8170823 := by decide
  rcases family_descends (prefixWord ++ tailWord_8170823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8170833 : List Nat := [1, 2, 2, 1, 4, 1, 4, 1, 3, 4]
def baseStart_8170833 : Nat := 118140960795 + 8170833 * 2 ^ 59
def prefixEnd_8170833 : Nat := 4983230072969 + 3 ^ 40 * 8170833 * 2
def baseEnd_8170833 : Nat := 1398521558872778437336843

theorem tailTrace_8170833 : CollatzResearch.WordTrace tailWord_8170833 prefixEnd_8170833 1398521558872778437336843 := by
  unfold tailWord_8170833
  simp only [CollatzResearch.WordTrace]
  refine ⟨298014762407474983022693153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198676508271649988681795435 298014762407474983022693153)
  ·
    refine ⟨223511071805606237267019865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298014762407474983022693153 223511071805606237267019865)
    ·
      refine ⟨167633303854204677950264899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223511071805606237267019865 167633303854204677950264899)
      ·
        refine ⟨251449955781307016925397349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167633303854204677950264899 251449955781307016925397349)
        ·
          refine ⟨47146866708995065673512003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 251449955781307016925397349 47146866708995065673512003)
          ·
            refine ⟨70720300063492598510268005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47146866708995065673512003 70720300063492598510268005)
            ·
              refine ⟨13260056261904862220675251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70720300063492598510268005 13260056261904862220675251)
              ·
                refine ⟨19890084392857293331012877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13260056261904862220675251 19890084392857293331012877)
                ·
                  refine ⟨7458781647321484999129829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19890084392857293331012877 7458781647321484999129829)
                  ·
                    refine ⟨1398521558872778437336843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7458781647321484999129829 1398521558872778437336843)
                    ·
                      rfl

theorem cell23_8170833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 3, 4].length) (baseStart_8170833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8170833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8170833 prefixEnd_8170833 := by exact prefixLift 8170833
  have htrace : WordTrace (prefixWord ++ tailWord_8170833) baseStart_8170833 baseEnd_8170833 := by
    simpa [prefixWord, tailWord_8170833, baseEnd_8170833] using wordTrace_append hprefix tailTrace_8170833
  have hstable : (prefixWord ++ tailWord_8170833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8170833).length < 2 ^ (prefixWord ++ tailWord_8170833).sum := by decide
  have hdescent : baseEnd_8170833 < baseStart_8170833 := by decide
  rcases family_descends (prefixWord ++ tailWord_8170833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8170836 : List Nat := [2, 4, 1, 1, 2, 1, 1, 2, 2, 1, 6]
def baseStart_8170836 : Nat := 118140960795 + 8170836 * 2 ^ 59
def prefixEnd_8170836 : Nat := 4983230072969 + 3 ^ 40 * 8170836 * 2
def baseEnd_8170836 : Nat := 4195566217060298800273015

theorem tailTrace_8170836 : CollatzResearch.WordTrace tailWord_8170836 prefixEnd_8170836 4195566217060298800273015 := by
  unfold tailWord_8170836
  simp only [CollatzResearch.WordTrace]
  refine ⟨149007435913232057267526181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198676581217642743023368241 149007435913232057267526181)
  ·
    refine ⟨27938894233731010737661159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149007435913232057267526181 27938894233731010737661159)
    ·
      refine ⟨41908341350596516106491739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27938894233731010737661159 41908341350596516106491739)
      ·
        refine ⟨62862512025894774159737609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41908341350596516106491739 62862512025894774159737609)
        ·
          refine ⟨47146884019421080619803207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62862512025894774159737609 47146884019421080619803207)
          ·
            refine ⟨70720326029131620929704811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47146884019421080619803207 70720326029131620929704811)
            ·
              refine ⟨106080489043697431394557217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70720326029131620929704811 106080489043697431394557217)
              ·
                refine ⟨79560366782773073545917913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106080489043697431394557217 79560366782773073545917913)
                ·
                  refine ⟨59670275087079805159438435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79560366782773073545917913 59670275087079805159438435)
                  ·
                    refine ⟨89505412630619707739157653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59670275087079805159438435 89505412630619707739157653)
                    ·
                      refine ⟨4195566217060298800273015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89505412630619707739157653 4195566217060298800273015)
                      ·
                        rfl

theorem cell23_8170836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_8170836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8170836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8170836 prefixEnd_8170836 := by exact prefixLift 8170836
  have htrace : WordTrace (prefixWord ++ tailWord_8170836) baseStart_8170836 baseEnd_8170836 := by
    simpa [prefixWord, tailWord_8170836, baseEnd_8170836] using wordTrace_append hprefix tailTrace_8170836
  have hstable : (prefixWord ++ tailWord_8170836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8170836).length < 2 ^ (prefixWord ++ tailWord_8170836).sum := by decide
  have hdescent : baseEnd_8170836 < baseStart_8170836 := by decide
  rcases family_descends (prefixWord ++ tailWord_8170836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8170873 : List Nat := [1, 2, 1, 3, 2, 1, 2, 2, 5, 1, 3]
def baseStart_8170873 : Nat := 118140960795 + 8170873 * 2 ^ 59
def prefixEnd_8170873 : Nat := 4983230072969 + 3 ^ 40 * 8170873 * 2
def baseEnd_8170873 : Nat := 4195585215844515155510345

theorem tailTrace_8170873 : CollatzResearch.WordTrace tailWord_8170873 prefixEnd_8170873 4195585215844515155510345 := by
  unfold tailWord_8170873
  simp only [CollatzResearch.WordTrace]
  refine ⟨298016221327330069854149273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198677480884886713236099515 298016221327330069854149273)
  ·
    refine ⟨223512165995497552390611955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298016221327330069854149273 223512165995497552390611955)
    ·
      refine ⟨335268248993246328585917933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223512165995497552390611955 335268248993246328585917933)
      ·
        refine ⟨125725593372467373219719225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335268248993246328585917933 125725593372467373219719225)
        ·
          refine ⟨94294195029350529914789419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125725593372467373219719225 94294195029350529914789419)
          ·
            refine ⟨141441292544025794872184129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94294195029350529914789419 141441292544025794872184129)
            ·
              refine ⟨106080969408019346154138097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141441292544025794872184129 106080969408019346154138097)
              ·
                refine ⟨79560727056014509615603573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106080969408019346154138097 79560727056014509615603573)
                ·
                  refine ⟨7458818161501360276462835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79560727056014509615603573 7458818161501360276462835)
                  ·
                    refine ⟨11188227242252040414694253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7458818161501360276462835 11188227242252040414694253)
                    ·
                      refine ⟨4195585215844515155510345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11188227242252040414694253 4195585215844515155510345)
                      ·
                        rfl

theorem cell23_8170873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 5, 1, 3].length) (baseStart_8170873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8170873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8170873 prefixEnd_8170873 := by exact prefixLift 8170873
  have htrace : WordTrace (prefixWord ++ tailWord_8170873) baseStart_8170873 baseEnd_8170873 := by
    simpa [prefixWord, tailWord_8170873, baseEnd_8170873] using wordTrace_append hprefix tailTrace_8170873
  have hstable : (prefixWord ++ tailWord_8170873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8170873).length < 2 ^ (prefixWord ++ tailWord_8170873).sum := by decide
  have hdescent : baseEnd_8170873 < baseStart_8170873 := by decide
  rcases family_descends (prefixWord ++ tailWord_8170873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8170930 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2]
def baseStart_8170930 : Nat := 118140960795 + 8170930 * 2 ^ 59
def prefixEnd_8170930 : Nat := 4983230072969 + 3 ^ 40 * 8170930 * 2
def baseEnd_8170930 : Nat := 4195614484241821432497583

theorem tailTrace_8170930 : CollatzResearch.WordTrace tailWord_8170930 prefixEnd_8170930 4195614484241821432497583 := by
  unfold tailWord_8170930
  simp only [CollatzResearch.WordTrace]
  refine ⟨74504575072030892147243561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198678866858749045725982829 74504575072030892147243561)
  ·
    refine ⟨55878431304023169110432671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74504575072030892147243561 55878431304023169110432671)
    ·
      refine ⟨83817646956034753665649007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55878431304023169110432671 83817646956034753665649007)
      ·
        refine ⟨125726470434052130498473511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83817646956034753665649007 125726470434052130498473511)
        ·
          refine ⟨188589705651078195747710267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125726470434052130498473511 188589705651078195747710267)
          ·
            refine ⟨282884558476617293621565401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188589705651078195747710267 282884558476617293621565401)
            ·
              refine ⟨212163418857462970216174051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282884558476617293621565401 212163418857462970216174051)
              ·
                refine ⟨318245128286194455324261077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212163418857462970216174051 318245128286194455324261077)
                ·
                  refine ⟨7458870194207682546662369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 318245128286194455324261077 7458870194207682546662369)
                  ·
                    refine ⟨5594152645655761909996777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7458870194207682546662369 5594152645655761909996777)
                    ·
                      refine ⟨4195614484241821432497583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5594152645655761909996777 4195614484241821432497583)
                      ·
                        rfl

theorem cell23_8170930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2].length) (baseStart_8170930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8170930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8170930 prefixEnd_8170930 := by exact prefixLift 8170930
  have htrace : WordTrace (prefixWord ++ tailWord_8170930) baseStart_8170930 baseEnd_8170930 := by
    simpa [prefixWord, tailWord_8170930, baseEnd_8170930] using wordTrace_append hprefix tailTrace_8170930
  have hstable : (prefixWord ++ tailWord_8170930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8170930).length < 2 ^ (prefixWord ++ tailWord_8170930).sum := by decide
  have hdescent : baseEnd_8170930 < baseStart_8170930 := by decide
  rcases family_descends (prefixWord ++ tailWord_8170930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8170964 : List Nat := [2, 4, 1, 2, 3, 1, 1, 2, 3, 2, 2]
def baseStart_8170964 : Nat := 118140960795 + 8170964 * 2 ^ 59
def prefixEnd_8170964 : Nat := 4983230072969 + 3 ^ 40 * 8170964 * 2
def baseEnd_8170964 : Nat := 4195631942584074299472427

theorem tailTrace_8170964 : CollatzResearch.WordTrace tailWord_8170964 prefixEnd_8170964 4195631942584074299472427 := by
  unfold tailWord_8170964
  simp only [CollatzResearch.WordTrace]
  refine ⟨149009770185000196197855973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198679693580000261597141297 149009770185000196197855973)
  ·
    refine ⟨27939331909687536787097995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149009770185000196197855973 27939331909687536787097995)
    ·
      refine ⟨41908997864531305180646993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27939331909687536787097995 41908997864531305180646993)
      ·
        refine ⟨31431748398398478885485245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41908997864531305180646993 31431748398398478885485245)
        ·
          refine ⟨11786905649399429582056967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31431748398398478885485245 11786905649399429582056967)
          ·
            refine ⟨17680358474099144373085451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11786905649399429582056967 17680358474099144373085451)
            ·
              refine ⟨26520537711148716559628177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17680358474099144373085451 26520537711148716559628177)
              ·
                refine ⟨19890403283361537419721133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26520537711148716559628177 19890403283361537419721133)
                ·
                  refine ⟨7458901231260576532395425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19890403283361537419721133 7458901231260576532395425)
                  ·
                    refine ⟨5594175923445432399296569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7458901231260576532395425 5594175923445432399296569)
                    ·
                      refine ⟨4195631942584074299472427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5594175923445432399296569 4195631942584074299472427)
                      ·
                        rfl

theorem cell23_8170964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_8170964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8170964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8170964 prefixEnd_8170964 := by exact prefixLift 8170964
  have htrace : WordTrace (prefixWord ++ tailWord_8170964) baseStart_8170964 baseEnd_8170964 := by
    simpa [prefixWord, tailWord_8170964, baseEnd_8170964] using wordTrace_append hprefix tailTrace_8170964
  have hstable : (prefixWord ++ tailWord_8170964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8170964).length < 2 ^ (prefixWord ++ tailWord_8170964).sum := by decide
  have hdescent : baseEnd_8170964 < baseStart_8170964 := by decide
  rcases family_descends (prefixWord ++ tailWord_8170964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8170981 : List Nat := [1, 3, 1, 5, 1, 2, 2, 3, 1, 2, 2]
def baseStart_8170981 : Nat := 118140960795 + 8170981 * 2 ^ 59
def prefixEnd_8170981 : Nat := 4983230072969 + 3 ^ 40 * 8170981 * 2
def baseEnd_8170981 : Nat := 4195640671755200732959849

theorem tailTrace_8170981 : CollatzResearch.WordTrace tailWord_8170981 prefixEnd_8170981 4195640671755200732959849 := by
  unfold tailWord_8170981
  simp only [CollatzResearch.WordTrace]
  refine ⟨298020160410938804299080797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198680106940625869532720531 298020160410938804299080797)
  ·
    refine ⟨111757560154102051612155299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298020160410938804299080797 111757560154102051612155299)
    ·
      refine ⟨167636340231153077418232949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111757560154102051612155299 167636340231153077418232949)
      ·
        refine ⟨15715906896670601007959339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167636340231153077418232949 15715906896670601007959339)
        ·
          refine ⟨23573860345005901511939009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15715906896670601007959339 23573860345005901511939009)
          ·
            refine ⟨17680395258754426133954257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23573860345005901511939009 17680395258754426133954257)
            ·
              refine ⟨13260296444065819600465693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17680395258754426133954257 13260296444065819600465693)
              ·
                refine ⟨4972611166524682350174635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13260296444065819600465693 4972611166524682350174635)
                ·
                  refine ⟨7458916749787023525261953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4972611166524682350174635 7458916749787023525261953)
                  ·
                    refine ⟨5594187562340267643946465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7458916749787023525261953 5594187562340267643946465)
                    ·
                      refine ⟨4195640671755200732959849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5594187562340267643946465 4195640671755200732959849)
                      ·
                        rfl

theorem cell23_8170981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_8170981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8170981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8170981 prefixEnd_8170981 := by exact prefixLift 8170981
  have htrace : WordTrace (prefixWord ++ tailWord_8170981) baseStart_8170981 baseEnd_8170981 := by
    simpa [prefixWord, tailWord_8170981, baseEnd_8170981] using wordTrace_append hprefix tailTrace_8170981
  have hstable : (prefixWord ++ tailWord_8170981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8170981).length < 2 ^ (prefixWord ++ tailWord_8170981).sum := by decide
  have hdescent : baseEnd_8170981 < baseStart_8170981 := by decide
  rcases family_descends (prefixWord ++ tailWord_8170981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171021 : List Nat := [1, 7, 1, 1, 3, 1, 2, 7]
def baseStart_8171021 : Nat := 118140960795 + 8171021 * 2 ^ 59
def prefixEnd_8171021 : Nat := 4983230072969 + 3 ^ 40 * 8171021 * 2
def baseEnd_8171021 : Nat := 155394859665977058387395

theorem tailTrace_8171021 : CollatzResearch.WordTrace tailWord_8171021 prefixEnd_8171021 155394859665977058387395 := by
  unfold tailWord_8171021
  simp only [CollatzResearch.WordTrace]
  refine ⟨298021619330793891130536917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198681079553862594087024611 298021619330793891130536917)
  ·
    refine ⟨6984881703065481823371959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 298021619330793891130536917 6984881703065481823371959)
    ·
      refine ⟨10477322554598222735057939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6984881703065481823371959 10477322554598222735057939)
      ·
        refine ⟨15715983831897334102586909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10477322554598222735057939 15715983831897334102586909)
        ·
          refine ⟨5893493936961500288470091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15715983831897334102586909 5893493936961500288470091)
          ·
            refine ⟨8840240905442250432705137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5893493936961500288470091 8840240905442250432705137)
            ·
              refine ⟨6630180679081687824528853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8840240905442250432705137 6630180679081687824528853)
              ·
                refine ⟨155394859665977058387395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6630180679081687824528853 155394859665977058387395)
                ·
                  rfl

theorem cell23_8171021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 7].length) (baseStart_8171021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171021 prefixEnd_8171021 := by exact prefixLift 8171021
  have htrace : WordTrace (prefixWord ++ tailWord_8171021) baseStart_8171021 baseEnd_8171021 := by
    simpa [prefixWord, tailWord_8171021, baseEnd_8171021] using wordTrace_append hprefix tailTrace_8171021
  have hstable : (prefixWord ++ tailWord_8171021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171021).length < 2 ^ (prefixWord ++ tailWord_8171021).sum := by decide
  have hdescent : baseEnd_8171021 < baseStart_8171021 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171037 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 6, 2, 2]
def baseStart_8171037 : Nat := 118140960795 + 8171037 * 2 ^ 59
def prefixEnd_8171037 : Nat := 4983230072969 + 3 ^ 40 * 8171037 * 2
def baseEnd_8171037 : Nat := 4195669426671852513859591

theorem tailTrace_8171037 : CollatzResearch.WordTrace tailWord_8171037 prefixEnd_8171037 4195669426671852513859591 := by
  unfold tailWord_8171037
  simp only [CollatzResearch.WordTrace]
  refine ⟨298022202898735925863119365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198681468599157283908746243 298022202898735925863119365)
  ·
    refine ⟨55879163043512986099334881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298022202898735925863119365 55879163043512986099334881)
    ·
      refine ⟨41909372282634739574501161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55879163043512986099334881 41909372282634739574501161)
      ·
        refine ⟨31432029211976054680875871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41909372282634739574501161 31432029211976054680875871)
        ·
          refine ⟨47148043817964082021313807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31432029211976054680875871 47148043817964082021313807)
          ·
            refine ⟨70722065726946123031970711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47148043817964082021313807 70722065726946123031970711)
            ·
              refine ⟨106083098590419184547956067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70722065726946123031970711 106083098590419184547956067)
              ·
                refine ⟨159124647885628776821934101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106083098590419184547956067 159124647885628776821934101)
                ·
                  refine ⟨7458967869638848913528161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 159124647885628776821934101 7458967869638848913528161)
                  ·
                    refine ⟨5594225902229136685146121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7458967869638848913528161 5594225902229136685146121)
                    ·
                      refine ⟨4195669426671852513859591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5594225902229136685146121 4195669426671852513859591)
                      ·
                        rfl

theorem cell23_8171037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_8171037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171037 prefixEnd_8171037 := by exact prefixLift 8171037
  have htrace : WordTrace (prefixWord ++ tailWord_8171037) baseStart_8171037 baseEnd_8171037 := by
    simpa [prefixWord, tailWord_8171037, baseEnd_8171037] using wordTrace_append hprefix tailTrace_8171037
  have hstable : (prefixWord ++ tailWord_8171037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171037).length < 2 ^ (prefixWord ++ tailWord_8171037).sum := by decide
  have hdescent : baseEnd_8171037 < baseStart_8171037 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171040 : List Nat := [2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 5]
def baseStart_8171040 : Nat := 118140960795 + 8171040 * 2 ^ 59
def prefixEnd_8171040 : Nat := 4983230072969 + 3 ^ 40 * 8171040 * 2
def baseEnd_8171040 : Nat := 4195670967113816002122077

theorem tailTrace_8171040 : CollatzResearch.WordTrace tailWord_8171040 prefixEnd_8171040 4195670967113816002122077 := by
  unfold tailWord_8171040
  simp only [CollatzResearch.WordTrace]
  refine ⟨149011156158862528687739287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198681541545150038250319049 149011156158862528687739287)
  ·
    refine ⟨223516734238293793031608931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149011156158862528687739287 223516734238293793031608931)
    ·
      refine ⟨335275101357440689547413397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223516734238293793031608931 335275101357440689547413397)
      ·
        refine ⟨15716020376130032322535003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 335275101357440689547413397 15716020376130032322535003)
        ·
          refine ⟨23574030564195048483802505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15716020376130032322535003 23574030564195048483802505)
          ·
            refine ⟨17680522923146286362851879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23574030564195048483802505 17680522923146286362851879)
            ·
              refine ⟨26520784384719429544277819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17680522923146286362851879 26520784384719429544277819)
              ·
                refine ⟨39781176577079144316416729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26520784384719429544277819 39781176577079144316416729)
                ·
                  refine ⟨29835882432809358237312547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39781176577079144316416729 29835882432809358237312547)
                  ·
                    refine ⟨44753823649214037355968821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29835882432809358237312547 44753823649214037355968821)
                    ·
                      refine ⟨4195670967113816002122077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44753823649214037355968821 4195670967113816002122077)
                      ·
                        rfl

theorem cell23_8171040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_8171040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171040 prefixEnd_8171040 := by exact prefixLift 8171040
  have htrace : WordTrace (prefixWord ++ tailWord_8171040) baseStart_8171040 baseEnd_8171040 := by
    simpa [prefixWord, tailWord_8171040, baseEnd_8171040] using wordTrace_append hprefix tailTrace_8171040
  have hstable : (prefixWord ++ tailWord_8171040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171040).length < 2 ^ (prefixWord ++ tailWord_8171040).sum := by decide
  have hdescent : baseEnd_8171040 < baseStart_8171040 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171054 : List Nat := [4, 1, 3, 1, 2, 1, 2, 1, 4, 2, 2]
def baseStart_8171054 : Nat := 118140960795 + 8171054 * 2 ^ 59
def prefixEnd_8171054 : Nat := 4983230072969 + 3 ^ 40 * 8171054 * 2
def baseEnd_8171054 : Nat := 4195678155842978947347013

theorem tailTrace_8171054 : CollatzResearch.WordTrace tailWord_8171054 prefixEnd_8171054 4195678155842978947347013 := by
  unfold tailWord_8171054
  simp only [CollatzResearch.WordTrace]
  refine ⟨37252852867459292220811027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198681881959782891844325477 37252852867459292220811027)
  ·
    refine ⟨55879279301188938331216541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37252852867459292220811027 55879279301188938331216541)
    ·
      refine ⟨20954729737945851874206203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55879279301188938331216541 20954729737945851874206203)
      ·
        refine ⟨31432094606918777811309305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20954729737945851874206203 31432094606918777811309305)
        ·
          refine ⟨23574070955189083358481979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31432094606918777811309305 23574070955189083358481979)
          ·
            refine ⟨35361106432783625037722969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23574070955189083358481979 35361106432783625037722969)
            ·
              refine ⟨26520829824587718778292227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35361106432783625037722969 26520829824587718778292227)
              ·
                refine ⟨39781244736881578167438341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26520829824587718778292227 39781244736881578167438341)
                ·
                  refine ⟨7458983388165295906394689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39781244736881578167438341 7458983388165295906394689)
                  ·
                    refine ⟨5594237541123971929796017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7458983388165295906394689 5594237541123971929796017)
                    ·
                      refine ⟨4195678155842978947347013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5594237541123971929796017 4195678155842978947347013)
                      ·
                        rfl

theorem cell23_8171054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_8171054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171054 prefixEnd_8171054 := by exact prefixLift 8171054
  have htrace : WordTrace (prefixWord ++ tailWord_8171054) baseStart_8171054 baseEnd_8171054 := by
    simpa [prefixWord, tailWord_8171054, baseEnd_8171054] using wordTrace_append hprefix tailTrace_8171054
  have hstable : (prefixWord ++ tailWord_8171054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171054).length < 2 ^ (prefixWord ++ tailWord_8171054).sum := by decide
  have hdescent : baseEnd_8171054 < baseStart_8171054 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171071 : List Nat := [1, 1, 2, 2, 3, 5, 2, 1, 2, 2, 2]
def baseStart_8171071 : Nat := 118140960795 + 8171071 * 2 ^ 59
def prefixEnd_8171071 : Nat := 4983230072969 + 3 ^ 40 * 8171071 * 2
def baseEnd_8171071 : Nat := 4195686885014105380834435

theorem tailTrace_8171071 : CollatzResearch.WordTrace tailWord_8171071 prefixEnd_8171071 4195686885014105380834435 := by
  unfold tailWord_8171071
  simp only [CollatzResearch.WordTrace]
  refine ⟨298023442980612749669857067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198682295320408499779904711 298023442980612749669857067)
  ·
    refine ⟨447035164470919124504785601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298023442980612749669857067 447035164470919124504785601)
    ·
      refine ⟨335276373353189343378589201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447035164470919124504785601 335276373353189343378589201)
      ·
        refine ⟨251457280014892007533941901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335276373353189343378589201 251457280014892007533941901)
        ·
          refine ⟨94296480005584502825228213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251457280014892007533941901 94296480005584502825228213)
          ·
            refine ⟨8840295000523547139865145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94296480005584502825228213 8840295000523547139865145)
            ·
              refine ⟨6630221250392660354898859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8840295000523547139865145 6630221250392660354898859)
              ·
                refine ⟨9945331875588990532348289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6630221250392660354898859 9945331875588990532348289)
                ·
                  refine ⟨7458998906691742899261217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9945331875588990532348289 7458998906691742899261217)
                  ·
                    refine ⟨5594249180018807174445913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7458998906691742899261217 5594249180018807174445913)
                    ·
                      refine ⟨4195686885014105380834435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5594249180018807174445913 4195686885014105380834435)
                      ·
                        rfl

theorem cell23_8171071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 1, 2, 2, 2].length) (baseStart_8171071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171071 prefixEnd_8171071 := by exact prefixLift 8171071
  have htrace : WordTrace (prefixWord ++ tailWord_8171071) baseStart_8171071 baseEnd_8171071 := by
    simpa [prefixWord, tailWord_8171071, baseEnd_8171071] using wordTrace_append hprefix tailTrace_8171071
  have hstable : (prefixWord ++ tailWord_8171071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171071).length < 2 ^ (prefixWord ++ tailWord_8171071).sum := by decide
  have hdescent : baseEnd_8171071 < baseStart_8171071 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171090 : List Nat := [3, 2, 2, 1, 2, 2, 1, 3, 2, 5]
def baseStart_8171090 : Nat := 118140960795 + 8171090 * 2 ^ 59
def prefixEnd_8171090 : Nat := 4983230072969 + 3 ^ 40 * 8171090 * 2
def baseEnd_8171090 : Nat := 1398565547048846935498949

theorem tailTrace_8171090 : CollatzResearch.WordTrace tailWord_8171090 prefixEnd_8171090 1398565547048846935498949 := by
  unfold tailWord_8171090
  simp only [CollatzResearch.WordTrace]
  refine ⟨74506033991885978978699681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198682757311695943943199149 74506033991885978978699681)
  ·
    refine ⟨55879525493914484234024761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74506033991885978978699681 55879525493914484234024761)
    ·
      refine ⟨41909644120435863175518571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55879525493914484234024761 41909644120435863175518571)
      ·
        refine ⟨62864466180653794763277857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41909644120435863175518571 62864466180653794763277857)
        ·
          refine ⟨47148349635490346072458393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62864466180653794763277857 47148349635490346072458393)
          ·
            refine ⟨35361262226617759554343795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47148349635490346072458393 35361262226617759554343795)
            ·
              refine ⟨53041893339926639331515693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35361262226617759554343795 53041893339926639331515693)
              ·
                refine ⟨19890710002472489749318385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53041893339926639331515693 19890710002472489749318385)
                ·
                  refine ⟨14918032501854367311988789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19890710002472489749318385 14918032501854367311988789)
                  ·
                    refine ⟨1398565547048846935498949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14918032501854367311988789 1398565547048846935498949)
                    ·
                      rfl

theorem cell23_8171090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_8171090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171090 prefixEnd_8171090 := by exact prefixLift 8171090
  have htrace : WordTrace (prefixWord ++ tailWord_8171090) baseStart_8171090 baseEnd_8171090 := by
    simpa [prefixWord, tailWord_8171090, baseEnd_8171090] using wordTrace_append hprefix tailTrace_8171090
  have hstable : (prefixWord ++ tailWord_8171090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171090).length < 2 ^ (prefixWord ++ tailWord_8171090).sum := by decide
  have hdescent : baseEnd_8171090 < baseStart_8171090 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171100 : List Nat := [2, 2, 4, 1, 2, 1, 1, 2, 1, 2, 5]
def baseStart_8171100 : Nat := 118140960795 + 8171100 * 2 ^ 59
def prefixEnd_8171100 : Nat := 4983230072969 + 3 ^ 40 * 8171100 * 2
def baseEnd_8171100 : Nat := 4195701775953085767371801

theorem tailTrace_8171100 : CollatzResearch.WordTrace tailWord_8171100 prefixEnd_8171100 4195701775953085767371801 := by
  unfold tailWord_8171100
  simp only [CollatzResearch.WordTrace]
  refine ⟨149012250348753843811331377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198683000465005125081775169 149012250348753843811331377)
  ·
    refine ⟨111759187761565382858498533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149012250348753843811331377 111759187761565382858498533)
    ·
      refine ⟨20954847705293509285968475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111759187761565382858498533 20954847705293509285968475)
      ·
        refine ⟨31432271557940263928952713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20954847705293509285968475 31432271557940263928952713)
        ·
          refine ⟨23574203668455197946714535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31432271557940263928952713 23574203668455197946714535)
          ·
            refine ⟨35361305502682796920071803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23574203668455197946714535 35361305502682796920071803)
            ·
              refine ⟨53041958254024195380107705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35361305502682796920071803 53041958254024195380107705)
              ·
                refine ⟨39781468690518146535080779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53041958254024195380107705 39781468690518146535080779)
                ·
                  refine ⟨59672203035777219802621169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39781468690518146535080779 59672203035777219802621169)
                  ·
                    refine ⟨44754152276832914851965877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59672203035777219802621169 44754152276832914851965877)
                    ·
                      refine ⟨4195701775953085767371801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44754152276832914851965877 4195701775953085767371801)
                      ·
                        rfl

theorem cell23_8171100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_8171100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171100 prefixEnd_8171100 := by exact prefixLift 8171100
  have htrace : WordTrace (prefixWord ++ tailWord_8171100) baseStart_8171100 baseEnd_8171100 := by
    simpa [prefixWord, tailWord_8171100, baseEnd_8171100] using wordTrace_append hprefix tailTrace_8171100
  have hstable : (prefixWord ++ tailWord_8171100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171100).length < 2 ^ (prefixWord ++ tailWord_8171100).sum := by decide
  have hdescent : baseEnd_8171100 < baseStart_8171100 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171137 : List Nat := [1, 2, 4, 2, 1, 3, 1, 2, 3, 4]
def baseStart_8171137 : Nat := 118140960795 + 8171137 * 2 ^ 59
def prefixEnd_8171137 : Nat := 4983230072969 + 3 ^ 40 * 8171137 * 2
def baseEnd_8171137 : Nat := 1398573591579100707536377

theorem tailTrace_8171137 : CollatzResearch.WordTrace tailWord_8171137 prefixEnd_8171137 1398573591579100707536377 := by
  unfold tailWord_8171137
  simp only [CollatzResearch.WordTrace]
  refine ⟨298025850198373642941759665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198683900132249095294506443 298025850198373642941759665)
  ·
    refine ⟨223519387648780232206319749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298025850198373642941759665 223519387648780232206319749)
    ·
      refine ⟨41909885184146293538684953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223519387648780232206319749 41909885184146293538684953)
      ·
        refine ⟨31432413888109720154013715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41909885184146293538684953 31432413888109720154013715)
        ·
          refine ⟨47148620832164580231020573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31432413888109720154013715 47148620832164580231020573)
          ·
            refine ⟨17680732812061717586632715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47148620832164580231020573 17680732812061717586632715)
            ·
              refine ⟨26521099218092576379949073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17680732812061717586632715 26521099218092576379949073)
              ·
                refine ⟨19890824413569432284961805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26521099218092576379949073 19890824413569432284961805)
                ·
                  refine ⟨7459059155088537106860677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19890824413569432284961805 7459059155088537106860677)
                  ·
                    refine ⟨1398573591579100707536377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7459059155088537106860677 1398573591579100707536377)
                    ·
                      rfl

theorem cell23_8171137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_8171137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171137 prefixEnd_8171137 := by exact prefixLift 8171137
  have htrace : WordTrace (prefixWord ++ tailWord_8171137) baseStart_8171137 baseEnd_8171137 := by
    simpa [prefixWord, tailWord_8171137, baseEnd_8171137] using wordTrace_append hprefix tailTrace_8171137
  have hstable : (prefixWord ++ tailWord_8171137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171137).length < 2 ^ (prefixWord ++ tailWord_8171137).sum := by decide
  have hdescent : baseEnd_8171137 < baseStart_8171137 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171167 : List Nat := [1, 1, 2, 7, 1, 1, 1, 1, 8]
def baseStart_8171167 : Nat := 118140960795 + 8171167 * 2 ^ 59
def prefixEnd_8171167 : Nat := 4983230072969 + 3 ^ 40 * 8171167 * 2
def baseEnd_8171167 : Nat := 466192908795215222803777

theorem tailTrace_8171167 : CollatzResearch.WordTrace tailWord_8171167 prefixEnd_8171167 466192908795215222803777 := by
  unfold tailWord_8171167
  simp only [CollatzResearch.WordTrace]
  refine ⟨298026944388264958065351755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198684629592176638710234503 298026944388264958065351755)
  ·
    refine ⟨447040416582397437098027633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298026944388264958065351755 447040416582397437098027633)
    ·
      refine ⟨335280312436798077823520725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447040416582397437098027633 335280312436798077823520725)
      ·
        refine ⟨7858132322737454948988767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 335280312436798077823520725 7858132322737454948988767)
        ·
          refine ⟨11787198484106182423483151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7858132322737454948988767 11787198484106182423483151)
          ·
            refine ⟨17680797726159273635224727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11787198484106182423483151 17680797726159273635224727)
            ·
              refine ⟨26521196589238910452837091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17680797726159273635224727 26521196589238910452837091)
              ·
                refine ⟨39781794883858365679255637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26521196589238910452837091 39781794883858365679255637)
                ·
                  refine ⟨466192908795215222803777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39781794883858365679255637 466192908795215222803777)
                  ·
                    rfl

theorem cell23_8171167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 8].length) (baseStart_8171167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171167 prefixEnd_8171167 := by exact prefixLift 8171167
  have htrace : WordTrace (prefixWord ++ tailWord_8171167) baseStart_8171167 baseEnd_8171167 := by
    simpa [prefixWord, tailWord_8171167, baseEnd_8171167] using wordTrace_append hprefix tailTrace_8171167
  have hstable : (prefixWord ++ tailWord_8171167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171167).length < 2 ^ (prefixWord ++ tailWord_8171167).sum := by decide
  have hdescent : baseEnd_8171167 < baseStart_8171167 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171197 : List Nat := [1, 4, 1, 2, 1, 2, 4, 2, 1, 5]
def baseStart_8171197 : Nat := 118140960795 + 8171197 * 2 ^ 59
def prefixEnd_8171197 : Nat := 4983230072969 + 3 ^ 40 * 8171197 * 2
def baseEnd_8171197 : Nat := 1398583861192190629286285

theorem tailTrace_8171197 : CollatzResearch.WordTrace tailWord_8171197 prefixEnd_8171197 1398583861192190629286285 := by
  unfold tailWord_8171197
  simp only [CollatzResearch.WordTrace]
  refine ⟨298028038578156273188943845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198685359052104182125962563 298028038578156273188943845)
  ·
    refine ⟨55880257233404301222926971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298028038578156273188943845 55880257233404301222926971)
    ·
      refine ⟨83820385850106451834390457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55880257233404301222926971 83820385850106451834390457)
      ·
        refine ⟨62865289387579838875792843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83820385850106451834390457 62865289387579838875792843)
        ·
          refine ⟨94297934081369758313689265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62865289387579838875792843 94297934081369758313689265)
          ·
            refine ⟨70723450561027318735266949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94297934081369758313689265 70723450561027318735266949)
            ·
              refine ⟨13260646980192622262862553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70723450561027318735266949 13260646980192622262862553)
              ·
                refine ⟨9945485235144466697146915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13260646980192622262862553 9945485235144466697146915)
                ·
                  refine ⟨14918227852716700045720373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9945485235144466697146915 14918227852716700045720373)
                  ·
                    refine ⟨1398583861192190629286285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14918227852716700045720373 1398583861192190629286285)
                    ·
                      rfl

theorem cell23_8171197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2, 1, 5].length) (baseStart_8171197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171197 prefixEnd_8171197 := by exact prefixLift 8171197
  have htrace : WordTrace (prefixWord ++ tailWord_8171197) baseStart_8171197 baseEnd_8171197 := by
    simpa [prefixWord, tailWord_8171197, baseEnd_8171197] using wordTrace_append hprefix tailTrace_8171197
  have hstable : (prefixWord ++ tailWord_8171197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171197).length < 2 ^ (prefixWord ++ tailWord_8171197).sum := by decide
  have hdescent : baseEnd_8171197 < baseStart_8171197 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171204 : List Nat := [2, 3, 3, 1, 1, 1, 2, 3, 2, 3, 2]
def baseStart_8171204 : Nat := 118140960795 + 8171204 * 2 ^ 59
def prefixEnd_8171204 : Nat := 4983230072969 + 3 ^ 40 * 8171204 * 2
def baseEnd_8171204 : Nat := 4195755177941153360471323

theorem tailTrace_8171204 : CollatzResearch.WordTrace tailWord_8171204 prefixEnd_8171204 4195755177941153360471323 := by
  unfold tailWord_8171204
  simp only [CollatzResearch.WordTrace]
  refine ⟨149014146944565456692224333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198685529259420608922965777 149014146944565456692224333)
  ·
    refine ⟨55880305104212046259584125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149014146944565456692224333 55880305104212046259584125)
    ·
      refine ⟨20955114414079517347344047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55880305104212046259584125 20955114414079517347344047)
      ·
        refine ⟨31432671621119276021016071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20955114414079517347344047 31432671621119276021016071)
        ·
          refine ⟨47149007431678914031524107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31432671621119276021016071 47149007431678914031524107)
          ·
            refine ⟨70723511147518371047286161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47149007431678914031524107 70723511147518371047286161)
            ·
              refine ⟨53042633360638778285464621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70723511147518371047286161 53042633360638778285464621)
              ·
                refine ⟨19890987510239541857049233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53042633360638778285464621 19890987510239541857049233)
                ·
                  refine ⟨14918240632679656392786925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19890987510239541857049233 14918240632679656392786925)
                  ·
                    refine ⟨5594340237254871147295097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14918240632679656392786925 5594340237254871147295097)
                    ·
                      refine ⟨4195755177941153360471323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5594340237254871147295097 4195755177941153360471323)
                      ·
                        rfl

theorem cell23_8171204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_8171204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171204 prefixEnd_8171204 := by exact prefixLift 8171204
  have htrace : WordTrace (prefixWord ++ tailWord_8171204) baseStart_8171204 baseEnd_8171204 := by
    simpa [prefixWord, tailWord_8171204, baseEnd_8171204] using wordTrace_append hprefix tailTrace_8171204
  have hstable : (prefixWord ++ tailWord_8171204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171204).length < 2 ^ (prefixWord ++ tailWord_8171204).sum := by decide
  have hdescent : baseEnd_8171204 < baseStart_8171204 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171217 : List Nat := [1, 2, 2, 1, 2, 4, 2, 3, 1, 1, 4]
def baseStart_8171217 : Nat := 118140960795 + 8171217 * 2 ^ 59
def prefixEnd_8171217 : Nat := 4983230072969 + 3 ^ 40 * 8171217 * 2
def baseEnd_8171217 : Nat := 4195761853189661809608763

theorem tailTrace_8171217 : CollatzResearch.WordTrace tailWord_8171217 prefixEnd_8171217 4195761853189661809608763 := by
  unfold tailWord_8171217
  simp only [CollatzResearch.WordTrace]
  refine ⟨298028768038083816604671905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198685845358722544403114603 298028768038083816604671905)
  ·
    refine ⟨223521576028562862453503929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298028768038083816604671905 223521576028562862453503929)
    ·
      refine ⟨167641182021422146840127947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223521576028562862453503929 167641182021422146840127947)
      ·
        refine ⟨251461773032133220260191921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167641182021422146840127947 251461773032133220260191921)
        ·
          refine ⟨188596329774099915195143941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251461773032133220260191921 188596329774099915195143941)
          ·
            refine ⟨35361811832643734099089489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188596329774099915195143941 35361811832643734099089489)
            ·
              refine ⟨26521358874482800574317117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35361811832643734099089489 26521358874482800574317117)
              ·
                refine ⟨9945509577931050215368919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26521358874482800574317117 9945509577931050215368919)
                ·
                  refine ⟨14918264366896575323053379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9945509577931050215368919 14918264366896575323053379)
                  ·
                    refine ⟨22377396550344862984580069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14918264366896575323053379 22377396550344862984580069)
                    ·
                      refine ⟨4195761853189661809608763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22377396550344862984580069 4195761853189661809608763)
                      ·
                        rfl

theorem cell23_8171217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3, 1, 1, 4].length) (baseStart_8171217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171217 prefixEnd_8171217 := by exact prefixLift 8171217
  have htrace : WordTrace (prefixWord ++ tailWord_8171217) baseStart_8171217 baseEnd_8171217 := by
    simpa [prefixWord, tailWord_8171217, baseEnd_8171217] using wordTrace_append hprefix tailTrace_8171217
  have hstable : (prefixWord ++ tailWord_8171217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171217).length < 2 ^ (prefixWord ++ tailWord_8171217).sum := by decide
  have hdescent : baseEnd_8171217 < baseStart_8171217 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171228 : List Nat := [2, 2, 5, 1, 2, 2, 1, 1, 3, 1, 3]
def baseStart_8171228 : Nat := 118140960795 + 8171228 * 2 ^ 59
def prefixEnd_8171228 : Nat := 4983230072969 + 3 ^ 40 * 8171228 * 2
def baseEnd_8171228 : Nat := 4195767501476861266571213

theorem tailTrace_8171228 : CollatzResearch.WordTrace tailWord_8171228 prefixEnd_8171228 4195767501476861266571213 := by
  unfold tailWord_8171228
  simp only [CollatzResearch.WordTrace]
  refine ⟨149014584620521982741661169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198686112827362643655548225 149014584620521982741661169)
  ·
    refine ⟨111760938465391487056245877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149014584620521982741661169 111760938465391487056245877)
    ·
      refine ⟨10477587981130451911523051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111760938465391487056245877 10477587981130451911523051)
      ·
        refine ⟨15716381971695677867284577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10477587981130451911523051 15716381971695677867284577)
        ·
          refine ⟨11787286478771758400463433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15716381971695677867284577 11787286478771758400463433)
          ·
            refine ⟨8840464859078818800347575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11787286478771758400463433 8840464859078818800347575)
            ·
              refine ⟨13260697288618228200521363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8840464859078818800347575 13260697288618228200521363)
              ·
                refine ⟨19891045932927342300782045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13260697288618228200521363 19891045932927342300782045)
                ·
                  refine ⟨7459142224847753362793267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19891045932927342300782045 7459142224847753362793267)
                  ·
                    refine ⟨11188713337271630044189901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7459142224847753362793267 11188713337271630044189901)
                    ·
                      refine ⟨4195767501476861266571213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11188713337271630044189901 4195767501476861266571213)
                      ·
                        rfl

theorem cell23_8171228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_8171228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171228 prefixEnd_8171228 := by exact prefixLift 8171228
  have htrace : WordTrace (prefixWord ++ tailWord_8171228) baseStart_8171228 baseEnd_8171228 := by
    simpa [prefixWord, tailWord_8171228, baseEnd_8171228] using wordTrace_append hprefix tailTrace_8171228
  have hstable : (prefixWord ++ tailWord_8171228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171228).length < 2 ^ (prefixWord ++ tailWord_8171228).sum := by decide
  have hdescent : baseEnd_8171228 < baseStart_8171228 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171237 : List Nat := [1, 3, 1, 4, 1, 1, 2, 2, 3, 2, 3]
def baseStart_8171237 : Nat := 118140960795 + 8171237 * 2 ^ 59
def prefixEnd_8171237 : Nat := 4983230072969 + 3 ^ 40 * 8171237 * 2
def baseEnd_8171237 : Nat := 4195772122802751731358671

theorem tailTrace_8171237 : CollatzResearch.WordTrace tailWord_8171237 prefixEnd_8171237 4195772122802751731358671 := by
  unfold tailWord_8171237
  simp only [CollatzResearch.WordTrace]
  refine ⟨298029497498011360020399965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198686331665340906680266643 298029497498011360020399965)
  ·
    refine ⟨111761061561754260007649987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298029497498011360020399965 111761061561754260007649987)
    ·
      refine ⟨167641592342631390011474981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111761061561754260007649987 167641592342631390011474981)
      ·
        refine ⟨31432798564243385627151559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167641592342631390011474981 31432798564243385627151559)
        ·
          refine ⟨47149197846365078440727339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31432798564243385627151559 47149197846365078440727339)
          ·
            refine ⟨70723796769547617661091009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47149197846365078440727339 70723796769547617661091009)
            ·
              refine ⟨53042847577160713245818257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70723796769547617661091009 53042847577160713245818257)
              ·
                refine ⟨39782135682870534934363693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53042847577160713245818257 39782135682870534934363693)
                ·
                  refine ⟨14918300881076450600386385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39782135682870534934363693 14918300881076450600386385)
                  ·
                    refine ⟨11188725660807337950289789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14918300881076450600386385 11188725660807337950289789)
                    ·
                      refine ⟨4195772122802751731358671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11188725660807337950289789 4195772122802751731358671)
                      ·
                        rfl

theorem cell23_8171237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_8171237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171237 prefixEnd_8171237 := by exact prefixLift 8171237
  have htrace : WordTrace (prefixWord ++ tailWord_8171237) baseStart_8171237 baseEnd_8171237 := by
    simpa [prefixWord, tailWord_8171237, baseEnd_8171237] using wordTrace_append hprefix tailTrace_8171237
  have hstable : (prefixWord ++ tailWord_8171237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171237).length < 2 ^ (prefixWord ++ tailWord_8171237).sum := by decide
  have hdescent : baseEnd_8171237 < baseStart_8171237 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171240 : List Nat := [2, 1, 4, 1, 3, 1, 1, 10]
def baseStart_8171240 : Nat := 118140960795 + 8171240 * 2 ^ 59
def prefixEnd_8171240 : Nat := 4983230072969 + 3 ^ 40 * 8171240 * 2
def baseEnd_8171240 : Nat := 155399024564619082208191

theorem tailTrace_8171240 : CollatzResearch.WordTrace tailWord_8171240 prefixEnd_8171240 155399024564619082208191 := by
  unfold tailWord_8171240
  simp only [CollatzResearch.WordTrace]
  refine ⟨149014803458500245766379587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198686404611333661021839449 149014803458500245766379587)
  ·
    refine ⟨223522205187750368649569381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149014803458500245766379587 223522205187750368649569381)
    ·
      refine ⟨41910413472703194121794259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223522205187750368649569381 41910413472703194121794259)
      ·
        refine ⟨62865620209054791182691389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41910413472703194121794259 62865620209054791182691389)
        ·
          refine ⟨23574607578395546693509271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62865620209054791182691389 23574607578395546693509271)
          ·
            refine ⟨35361911367593320040263907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23574607578395546693509271 35361911367593320040263907)
            ·
              refine ⟨53042867051389980060395861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35361911367593320040263907 53042867051389980060395861)
              ·
                refine ⟨155399024564619082208191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 53042867051389980060395861 155399024564619082208191)
                ·
                  rfl

theorem cell23_8171240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 10].length) (baseStart_8171240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171240 prefixEnd_8171240 := by exact prefixLift 8171240
  have htrace : WordTrace (prefixWord ++ tailWord_8171240) baseStart_8171240 baseEnd_8171240 := by
    simpa [prefixWord, tailWord_8171240, baseEnd_8171240] using wordTrace_append hprefix tailTrace_8171240
  have hstable : (prefixWord ++ tailWord_8171240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171240).length < 2 ^ (prefixWord ++ tailWord_8171240).sum := by decide
  have hdescent : baseEnd_8171240 < baseStart_8171240 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171244 : List Nat := [2, 2, 1, 1, 2, 2, 6, 1, 2, 4]
def baseStart_8171244 : Nat := 118140960795 + 8171244 * 2 ^ 59
def prefixEnd_8171244 : Nat := 4983230072969 + 3 ^ 40 * 8171244 * 2
def baseEnd_8171244 : Nat := 1398591905722444401323713

theorem tailTrace_8171244 : CollatzResearch.WordTrace tailWord_8171244 prefixEnd_8171244 1398591905722444401323713 := by
  unfold tailWord_8171244
  simp only [CollatzResearch.WordTrace]
  refine ⟨149014876404493000107952393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198686501872657333477269857 149014876404493000107952393)
  ·
    refine ⟨111761157303369750080964295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149014876404493000107952393 111761157303369750080964295)
    ·
      refine ⟨167641735955054625121446443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111761157303369750080964295 167641735955054625121446443)
      ·
        refine ⟨251462603932581937682169665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167641735955054625121446443 251462603932581937682169665)
        ·
          refine ⟨188596952949436453261627249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251462603932581937682169665 188596952949436453261627249)
          ·
            refine ⟨141447714712077339946220437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188596952949436453261627249 141447714712077339946220437)
            ·
              refine ⟨6630361627128625309979083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 141447714712077339946220437 6630361627128625309979083)
              ·
                refine ⟨9945542440692937964968625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6630361627128625309979083 9945542440692937964968625)
                ·
                  refine ⟨7459156830519703473726469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9945542440692937964968625 7459156830519703473726469)
                  ·
                    refine ⟨1398591905722444401323713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7459156830519703473726469 1398591905722444401323713)
                    ·
                      rfl

theorem cell23_8171244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 4].length) (baseStart_8171244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171244 prefixEnd_8171244 := by exact prefixLift 8171244
  have htrace : WordTrace (prefixWord ++ tailWord_8171244) baseStart_8171244 baseEnd_8171244 := by
    simpa [prefixWord, tailWord_8171244, baseEnd_8171244] using wordTrace_append hprefix tailTrace_8171244
  have hstable : (prefixWord ++ tailWord_8171244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171244).length < 2 ^ (prefixWord ++ tailWord_8171244).sum := by decide
  have hdescent : baseEnd_8171244 < baseStart_8171244 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171254 : List Nat := [5, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3]
def baseStart_8171254 : Nat := 118140960795 + 8171254 * 2 ^ 59
def prefixEnd_8171254 : Nat := 4983230072969 + 3 ^ 40 * 8171254 * 2
def baseEnd_8171254 : Nat := 4195780851973878164846093

theorem tailTrace_8171254 : CollatzResearch.WordTrace tailWord_8171254 prefixEnd_8171254 4195780851973878164846093 := by
  unfold tailWord_8171254
  simp only [CollatzResearch.WordTrace]
  refine ⟨18626882346184360745235551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198686745025966514615845877 18626882346184360745235551)
  ·
    refine ⟨27940323519276541117853327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18626882346184360745235551 27940323519276541117853327)
    ·
      refine ⟨41910485278914811676779991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27940323519276541117853327 41910485278914811676779991)
      ·
        refine ⟨62865727918372217515169987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41910485278914811676779991 62865727918372217515169987)
        ·
          refine ⟨94298591877558326272754981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62865727918372217515169987 94298591877558326272754981)
          ·
            refine ⟨17680985977042186176141559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94298591877558326272754981 17680985977042186176141559)
            ·
              refine ⟨26521478965563279264212339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17680985977042186176141559 26521478965563279264212339)
              ·
                refine ⟨39782218448344918896318509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26521478965563279264212339 39782218448344918896318509)
                ·
                  refine ⟨14918331918129344586119441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39782218448344918896318509 14918331918129344586119441)
                  ·
                    refine ⟨11188748938597008439589581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14918331918129344586119441 11188748938597008439589581)
                    ·
                      refine ⟨4195780851973878164846093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11188748938597008439589581 4195780851973878164846093)
                      ·
                        rfl

theorem cell23_8171254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_8171254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171254 prefixEnd_8171254 := by exact prefixLift 8171254
  have htrace : WordTrace (prefixWord ++ tailWord_8171254) baseStart_8171254 baseEnd_8171254 := by
    simpa [prefixWord, tailWord_8171254, baseEnd_8171254] using wordTrace_append hprefix tailTrace_8171254
  have hstable : (prefixWord ++ tailWord_8171254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171254).length < 2 ^ (prefixWord ++ tailWord_8171254).sum := by decide
  have hdescent : baseEnd_8171254 < baseStart_8171254 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171267 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 6, 1, 3]
def baseStart_8171267 : Nat := 118140960795 + 8171267 * 2 ^ 59
def prefixEnd_8171267 : Nat := 4983230072969 + 3 ^ 40 * 8171267 * 2
def baseEnd_8171267 : Nat := 4195787527222386613983533

theorem tailTrace_8171267 : CollatzResearch.WordTrace tailWord_8171267 prefixEnd_8171267 4195787527222386613983533 := by
  unfold tailWord_8171267
  simp only [CollatzResearch.WordTrace]
  refine ⟨298030591687902675143992055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198687061125268450095994703 298030591687902675143992055)
  ·
    refine ⟨447045887531854012715988083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298030591687902675143992055 447045887531854012715988083)
    ·
      refine ⟨670568831297781019073982125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447045887531854012715988083 670568831297781019073982125)
      ·
        refine ⟨251463311736667882152743297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 670568831297781019073982125 251463311736667882152743297)
        ·
          refine ⟨188597483802500911614557473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251463311736667882152743297 188597483802500911614557473)
          ·
            refine ⟨141448112851875683710918105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188597483802500911614557473 141448112851875683710918105)
            ·
              refine ⟨106086084638906762783188579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141448112851875683710918105 106086084638906762783188579)
              ·
                refine ⟨159129126958360144174782869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106086084638906762783188579 159129126958360144174782869)
                ·
                  refine ⟨7459177826173131758192947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 159129126958360144174782869 7459177826173131758192947)
                  ·
                    refine ⟨11188766739259697637289421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7459177826173131758192947 11188766739259697637289421)
                    ·
                      refine ⟨4195787527222386613983533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11188766739259697637289421 4195787527222386613983533)
                      ·
                        rfl

theorem cell23_8171267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 6, 1, 3].length) (baseStart_8171267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171267 prefixEnd_8171267 := by exact prefixLift 8171267
  have htrace : WordTrace (prefixWord ++ tailWord_8171267) baseStart_8171267 baseEnd_8171267 := by
    simpa [prefixWord, tailWord_8171267, baseEnd_8171267] using wordTrace_append hprefix tailTrace_8171267
  have hstable : (prefixWord ++ tailWord_8171267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171267).length < 2 ^ (prefixWord ++ tailWord_8171267).sum := by decide
  have hdescent : baseEnd_8171267 < baseStart_8171267 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171271 : List Nat := [1, 1, 4, 4, 3, 1, 1, 1, 1, 1, 5]
def baseStart_8171271 : Nat := 118140960795 + 8171271 * 2 ^ 59
def prefixEnd_8171271 : Nat := 4983230072969 + 3 ^ 40 * 8171271 * 2
def baseEnd_8171271 : Nat := 4195789581145004598333515

theorem tailTrace_8171271 : CollatzResearch.WordTrace tailWord_8171271 prefixEnd_8171271 4195789581145004598333515 := by
  unfold tailWord_8171271
  simp only [CollatzResearch.WordTrace]
  refine ⟨298030737579888183827137667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198687158386592122551425111 298030737579888183827137667)
  ·
    refine ⟨447046106369832275740706501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298030737579888183827137667 447046106369832275740706501)
    ·
      refine ⟨83821144944343551701382469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 447046106369832275740706501 83821144944343551701382469)
      ·
        refine ⟨15716464677064415944009213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83821144944343551701382469 15716464677064415944009213)
        ·
          refine ⟨5893674253899155979003455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15716464677064415944009213 5893674253899155979003455)
          ·
            refine ⟨8840511380848733968505183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5893674253899155979003455 8840511380848733968505183)
            ·
              refine ⟨13260767071273100952757775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8840511380848733968505183 13260767071273100952757775)
              ·
                refine ⟨19891150606909651429136663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13260767071273100952757775 19891150606909651429136663)
                ·
                  refine ⟨29836725910364477143704995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19891150606909651429136663 29836725910364477143704995)
                  ·
                    refine ⟨44755088865546715715557493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29836725910364477143704995 44755088865546715715557493)
                    ·
                      refine ⟨4195789581145004598333515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44755088865546715715557493 4195789581145004598333515)
                      ·
                        rfl

theorem cell23_8171271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_8171271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171271 prefixEnd_8171271 := by exact prefixLift 8171271
  have htrace : WordTrace (prefixWord ++ tailWord_8171271) baseStart_8171271 baseEnd_8171271 := by
    simpa [prefixWord, tailWord_8171271, baseEnd_8171271] using wordTrace_append hprefix tailTrace_8171271
  have hstable : (prefixWord ++ tailWord_8171271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171271).length < 2 ^ (prefixWord ++ tailWord_8171271).sum := by decide
  have hdescent : baseEnd_8171271 < baseStart_8171271 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171285 : List Nat := [1, 3, 2, 1, 2, 5, 2, 2, 1, 2, 2]
def baseStart_8171285 : Nat := 118140960795 + 8171285 * 2 ^ 59
def prefixEnd_8171285 : Nat := 4983230072969 + 3 ^ 40 * 8171285 * 2
def baseEnd_8171285 : Nat := 4195796769874167543558451

theorem tailTrace_8171285 : CollatzResearch.WordTrace tailWord_8171285 prefixEnd_8171285 4195796769874167543558451 := by
  unfold tailWord_8171285
  simp only [CollatzResearch.WordTrace]
  refine ⟨298031248201837464218147309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198687498801224976145431539 298031248201837464218147309)
  ·
    refine ⟨111761718075689049081805241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298031248201837464218147309 111761718075689049081805241)
    ·
      refine ⟨83821288556766786811353931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111761718075689049081805241 83821288556766786811353931)
      ·
        refine ⟨125731932835150180217030897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83821288556766786811353931 125731932835150180217030897)
        ·
          refine ⟨94298949626362635162773173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125731932835150180217030897 94298949626362635162773173)
          ·
            refine ⟨8840526527471497046509985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94298949626362635162773173 8840526527471497046509985)
            ·
              refine ⟨6630394895603622784882489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8840526527471497046509985 6630394895603622784882489)
              ·
                refine ⟨4972796171702717088661867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6630394895603622784882489 4972796171702717088661867)
                ·
                  refine ⟨7459194257554075632992801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4972796171702717088661867 7459194257554075632992801)
                  ·
                    refine ⟨5594395693165556724744601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7459194257554075632992801 5594395693165556724744601)
                    ·
                      refine ⟨4195796769874167543558451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5594395693165556724744601 4195796769874167543558451)
                      ·
                        rfl

theorem cell23_8171285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 2, 1, 2, 2].length) (baseStart_8171285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171285 prefixEnd_8171285 := by exact prefixLift 8171285
  have htrace : WordTrace (prefixWord ++ tailWord_8171285) baseStart_8171285 baseEnd_8171285 := by
    simpa [prefixWord, tailWord_8171285, baseEnd_8171285] using wordTrace_append hprefix tailTrace_8171285
  have hstable : (prefixWord ++ tailWord_8171285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171285).length < 2 ^ (prefixWord ++ tailWord_8171285).sum := by decide
  have hdescent : baseEnd_8171285 < baseStart_8171285 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171324 : List Nat := [2, 2, 2, 2, 1, 1, 4, 2, 1, 4, 2]
def baseStart_8171324 : Nat := 118140960795 + 8171324 * 2 ^ 59
def prefixEnd_8171324 : Nat := 4983230072969 + 3 ^ 40 * 8171324 * 2
def baseEnd_8171324 : Nat := 4195816795619692890970771

theorem tailTrace_8171324 : CollatzResearch.WordTrace tailWord_8171324 prefixEnd_8171324 4195816795619692890970771 := by
  unfold tailWord_8171324
  simp only [CollatzResearch.WordTrace]
  refine ⟨149016335324348086939408513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198688447099130782585878017 149016335324348086939408513)
  ·
    refine ⟨111762251493261065204556385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149016335324348086939408513 111762251493261065204556385)
    ·
      refine ⟨83821688619945798903417289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111762251493261065204556385 83821688619945798903417289)
      ·
        refine ⟨62866266464959349177562967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83821688619945798903417289 62866266464959349177562967)
        ·
          refine ⟨94299399697439023766344451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62866266464959349177562967 94299399697439023766344451)
          ·
            refine ⟨141449099546158535649516677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94299399697439023766344451 141449099546158535649516677)
            ·
              refine ⟨26521706164904725434284377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141449099546158535649516677 26521706164904725434284377)
              ·
                refine ⟨19891279623678544075713283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26521706164904725434284377 19891279623678544075713283)
                ·
                  refine ⟨29836919435517816113569925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19891279623678544075713283 29836919435517816113569925)
                  ·
                    refine ⟨5594422394159590521294361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29836919435517816113569925 5594422394159590521294361)
                    ·
                      refine ⟨4195816795619692890970771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5594422394159590521294361 4195816795619692890970771)
                      ·
                        rfl

theorem cell23_8171324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 1, 4, 2].length) (baseStart_8171324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171324 prefixEnd_8171324 := by exact prefixLift 8171324
  have htrace : WordTrace (prefixWord ++ tailWord_8171324) baseStart_8171324 baseEnd_8171324 := by
    simpa [prefixWord, tailWord_8171324, baseEnd_8171324] using wordTrace_append hprefix tailTrace_8171324
  have hstable : (prefixWord ++ tailWord_8171324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171324).length < 2 ^ (prefixWord ++ tailWord_8171324).sum := by decide
  have hdescent : baseEnd_8171324 < baseStart_8171324 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171377 : List Nat := [1, 2, 2, 2, 1, 3, 2, 3, 2, 5]
def baseStart_8171377 : Nat := 118140960795 + 8171377 * 2 ^ 59
def prefixEnd_8171377 : Nat := 4983230072969 + 3 ^ 40 * 8171377 * 2
def baseEnd_8171377 : Nat := 1398614670031460394536009

theorem tailTrace_8171377 : CollatzResearch.WordTrace tailWord_8171377 prefixEnd_8171377 1398614670031460394536009 := by
  unfold tailWord_8171377
  simp only [CollatzResearch.WordTrace]
  refine ⟨298034603717504163930496385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198689735811669442620330923 298034603717504163930496385)
  ·
    refine ⟨223525952788128122947872289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298034603717504163930496385 223525952788128122947872289)
    ·
      refine ⟨167644464591096092210904217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223525952788128122947872289 167644464591096092210904217)
      ·
        refine ⟨125733348443322069158178163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167644464591096092210904217 125733348443322069158178163)
        ·
          refine ⟨188600022664983103737267245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125733348443322069158178163 188600022664983103737267245)
          ·
            refine ⟨70725008499368663901475217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188600022664983103737267245 70725008499368663901475217)
            ·
              refine ⟨53043756374526497926106413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70725008499368663901475217 53043756374526497926106413)
              ·
                refine ⟨19891408640447436722289905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53043756374526497926106413 19891408640447436722289905)
                ·
                  refine ⟨14918556480335577541717429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19891408640447436722289905 14918556480335577541717429)
                  ·
                    refine ⟨1398614670031460394536009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14918556480335577541717429 1398614670031460394536009)
                    ·
                      rfl

theorem cell23_8171377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2, 5].length) (baseStart_8171377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171377 prefixEnd_8171377 := by exact prefixLift 8171377
  have htrace : WordTrace (prefixWord ++ tailWord_8171377) baseStart_8171377 baseEnd_8171377 := by
    simpa [prefixWord, tailWord_8171377, baseEnd_8171377] using wordTrace_append hprefix tailTrace_8171377
  have hstable : (prefixWord ++ tailWord_8171377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171377).length < 2 ^ (prefixWord ++ tailWord_8171377).sum := by decide
  have hdescent : baseEnd_8171377 < baseStart_8171377 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171417 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 3, 4, 3]
def baseStart_8171417 : Nat := 118140960795 + 8171417 * 2 ^ 59
def prefixEnd_8171417 : Nat := 4983230072969 + 3 ^ 40 * 8171417 * 2
def baseEnd_8171417 : Nat := 4195864549320561027107843

theorem tailTrace_8171417 : CollatzResearch.WordTrace tailWord_8171417 prefixEnd_8171417 4195864549320561027107843 := by
  unfold tailWord_8171417
  simp only [CollatzResearch.WordTrace]
  refine ⟨298036062637359250761952505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198690708424906167174635003 298036062637359250761952505)
  ·
    refine ⟨223527046978019438071464379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298036062637359250761952505 223527046978019438071464379)
    ·
      refine ⟨335290570467029157107196569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223527046978019438071464379 335290570467029157107196569)
      ·
        refine ⟨251467927850271867830397427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335290570467029157107196569 251467927850271867830397427)
        ·
          refine ⟨377201891775407801745596141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251467927850271867830397427 377201891775407801745596141)
          ·
            refine ⟨141450709415777925654598553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 377201891775407801745596141 141450709415777925654598553)
            ·
              refine ⟨106088032061833444240948915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141450709415777925654598553 106088032061833444240948915)
              ·
                refine ⟨159132048092750166361423373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106088032061833444240948915 159132048092750166361423373)
                ·
                  refine ⟨59674518034781312385533765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159132048092750166361423373 59674518034781312385533765)
                  ·
                    refine ⟨11188972131521496072287581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59674518034781312385533765 11188972131521496072287581)
                    ·
                      refine ⟨4195864549320561027107843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11188972131521496072287581 4195864549320561027107843)
                      ·
                        rfl

theorem cell23_8171417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 4, 3].length) (baseStart_8171417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171417 prefixEnd_8171417 := by exact prefixLift 8171417
  have htrace : WordTrace (prefixWord ++ tailWord_8171417) baseStart_8171417 baseEnd_8171417 := by
    simpa [prefixWord, tailWord_8171417, baseEnd_8171417] using wordTrace_append hprefix tailTrace_8171417
  have hstable : (prefixWord ++ tailWord_8171417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171417).length < 2 ^ (prefixWord ++ tailWord_8171417).sum := by decide
  have hdescent : baseEnd_8171417 < baseStart_8171417 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171431 : List Nat := [1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 4]
def baseStart_8171431 : Nat := 118140960795 + 8171431 * 2 ^ 59
def prefixEnd_8171431 : Nat := 4983230072969 + 3 ^ 40 * 8171431 * 2
def baseEnd_8171431 : Nat := 4195871738049723972332779

theorem tailTrace_8171431 : CollatzResearch.WordTrace tailWord_8171431 prefixEnd_8171431 4195871738049723972332779 := by
  unfold tailWord_8171431
  simp only [CollatzResearch.WordTrace]
  refine ⟨298036573259308531152962147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198691048839539020768641431 298036573259308531152962147)
  ·
    refine ⟨447054859888962796729443221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298036573259308531152962147 447054859888962796729443221)
    ·
      refine ⟨20955696557295131096692651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 447054859888962796729443221 20955696557295131096692651)
      ·
        refine ⟨31433544835942696645038977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20955696557295131096692651 31433544835942696645038977)
        ·
          refine ⟨23575158626957022483779233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31433544835942696645038977 23575158626957022483779233)
          ·
            refine ⟨17681368970217766862834425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23575158626957022483779233 17681368970217766862834425)
            ·
              refine ⟨13261026727663325147125819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17681368970217766862834425 13261026727663325147125819)
              ·
                refine ⟨19891540091494987720688729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13261026727663325147125819 19891540091494987720688729)
                ·
                  refine ⟨14918655068621240790516547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19891540091494987720688729 14918655068621240790516547)
                  ·
                    refine ⟨22377982602931861185774821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14918655068621240790516547 22377982602931861185774821)
                    ·
                      refine ⟨4195871738049723972332779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22377982602931861185774821 4195871738049723972332779)
                      ·
                        rfl

theorem cell23_8171431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_8171431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171431 prefixEnd_8171431 := by exact prefixLift 8171431
  have htrace : WordTrace (prefixWord ++ tailWord_8171431) baseStart_8171431 baseEnd_8171431 := by
    simpa [prefixWord, tailWord_8171431, baseEnd_8171431] using wordTrace_append hprefix tailTrace_8171431
  have hstable : (prefixWord ++ tailWord_8171431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171431).length < 2 ^ (prefixWord ++ tailWord_8171431).sum := by decide
  have hdescent : baseEnd_8171431 < baseStart_8171431 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171454 : List Nat := [4, 2, 1, 1, 1, 3, 1, 4, 6]
def baseStart_8171454 : Nat := 118140960795 + 8171454 * 2 ^ 59
def prefixEnd_8171454 : Nat := 4983230072969 + 3 ^ 40 * 8171454 * 2
def baseEnd_8171454 : Nat := 466209283122753042482797

theorem tailTrace_8171454 : CollatzResearch.WordTrace tailWord_8171454 prefixEnd_8171454 466209283122753042482797 := by
  unfold tailWord_8171454
  simp only [CollatzResearch.WordTrace]
  refine ⟨37254676517278150760131177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198691608092150137387366277 37254676517278150760131177)
  ·
    refine ⟨27941007387958613070098383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37254676517278150760131177 27941007387958613070098383)
    ·
      refine ⟨41911511081937919605147575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27941007387958613070098383 41911511081937919605147575)
      ·
        refine ⟨62867266622906879407721363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41911511081937919605147575 62867266622906879407721363)
        ·
          refine ⟨94300899934360319111582045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62867266622906879407721363 94300899934360319111582045)
          ·
            refine ⟨35362837475385119666843267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94300899934360319111582045 35362837475385119666843267)
            ·
              refine ⟨53044256213077679500264901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35362837475385119666843267 53044256213077679500264901)
              ·
                refine ⟨9945798039952064906299669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53044256213077679500264901 9945798039952064906299669)
                ·
                  refine ⟨466209283122753042482797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9945798039952064906299669 466209283122753042482797)
                  ·
                    rfl

theorem cell23_8171454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_8171454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171454 prefixEnd_8171454 := by exact prefixLift 8171454
  have htrace : WordTrace (prefixWord ++ tailWord_8171454) baseStart_8171454 baseEnd_8171454 := by
    simpa [prefixWord, tailWord_8171454, baseEnd_8171454] using wordTrace_append hprefix tailTrace_8171454
  have hstable : (prefixWord ++ tailWord_8171454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171454).length < 2 ^ (prefixWord ++ tailWord_8171454).sum := by decide
  have hdescent : baseEnd_8171454 < baseStart_8171454 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171467 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 5, 5]
def baseStart_8171467 : Nat := 118140960795 + 8171467 * 2 ^ 59
def prefixEnd_8171467 : Nat := 4983230072969 + 3 ^ 40 * 8171467 * 2
def baseEnd_8171467 : Nat := 1398630074451095277160871

theorem tailTrace_8171467 : CollatzResearch.WordTrace tailWord_8171467 prefixEnd_8171467 1398630074451095277160871 := by
  unfold tailWord_8171467
  simp only [CollatzResearch.WordTrace]
  refine ⟨298037886287178109301272655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198691924191452072867515103 298037886287178109301272655)
  ·
    refine ⟨447056829430767163951908983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298037886287178109301272655 447056829430767163951908983)
    ·
      refine ⟨670585244146150745927863475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447056829430767163951908983 670585244146150745927863475)
      ·
        refine ⟨1005877866219226118891795213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 670585244146150745927863475 1005877866219226118891795213)
        ·
          refine ⟨377204199832209794584423205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1005877866219226118891795213 377204199832209794584423205)
          ·
            refine ⟨70725787468539336484579351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 377204199832209794584423205 70725787468539336484579351)
            ·
              refine ⟨106088681202809004726869027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70725787468539336484579351 106088681202809004726869027)
              ·
                refine ⟨159133021804213507090303541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106088681202809004726869027 159133021804213507090303541)
                ·
                  refine ⟨14918720794145016289715957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 159133021804213507090303541 14918720794145016289715957)
                  ·
                    refine ⟨1398630074451095277160871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14918720794145016289715957 1398630074451095277160871)
                    ·
                      rfl

theorem cell23_8171467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5, 5].length) (baseStart_8171467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171467 prefixEnd_8171467 := by exact prefixLift 8171467
  have htrace : WordTrace (prefixWord ++ tailWord_8171467) baseStart_8171467 baseEnd_8171467 := by
    simpa [prefixWord, tailWord_8171467, baseEnd_8171467] using wordTrace_append hprefix tailTrace_8171467
  have hstable : (prefixWord ++ tailWord_8171467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171467).length < 2 ^ (prefixWord ++ tailWord_8171467).sum := by decide
  have hdescent : baseEnd_8171467 < baseStart_8171467 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171485 : List Nat := [1, 4, 3, 1, 4, 1, 1, 1, 2, 2, 3]
def baseStart_8171485 : Nat := 118140960795 + 8171485 * 2 ^ 59
def prefixEnd_8171485 : Nat := 4983230072969 + 3 ^ 40 * 8171485 * 2
def baseEnd_8171485 : Nat := 4195899466005066761057531

theorem tailTrace_8171485 : CollatzResearch.WordTrace tailWord_8171485 prefixEnd_8171485 4195899466005066761057531 := by
  unfold tailWord_8171485
  simp only [CollatzResearch.WordTrace]
  refine ⟨298038542801112898375427909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198692361867408598916951939 298038542801112898375427909)
  ·
    refine ⟨55882226775208668445392733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298038542801112898375427909 55882226775208668445392733)
    ·
      refine ⟨20955835040703250667022275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55882226775208668445392733 20955835040703250667022275)
      ·
        refine ⟨31433752561054876000533413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20955835040703250667022275 31433752561054876000533413)
        ·
          refine ⟨5893828605197789250100015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31433752561054876000533413 5893828605197789250100015)
          ·
            refine ⟨8840742907796683875150023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5893828605197789250100015 8840742907796683875150023)
            ·
              refine ⟨13261114361695025812725035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8840742907796683875150023 13261114361695025812725035)
              ·
                refine ⟨19891671542542538719087553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13261114361695025812725035 19891671542542538719087553)
                ·
                  refine ⟨14918753656906904039315665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19891671542542538719087553 14918753656906904039315665)
                  ·
                    refine ⟨11189065242680178029486749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14918753656906904039315665 11189065242680178029486749)
                    ·
                      refine ⟨4195899466005066761057531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11189065242680178029486749 4195899466005066761057531)
                      ·
                        rfl

theorem cell23_8171485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_8171485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171485 prefixEnd_8171485 := by exact prefixLift 8171485
  have htrace : WordTrace (prefixWord ++ tailWord_8171485) baseStart_8171485 baseEnd_8171485 := by
    simpa [prefixWord, tailWord_8171485, baseEnd_8171485] using wordTrace_append hprefix tailTrace_8171485
  have hstable : (prefixWord ++ tailWord_8171485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171485).length < 2 ^ (prefixWord ++ tailWord_8171485).sum := by decide
  have hdescent : baseEnd_8171485 < baseStart_8171485 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171491 : List Nat := [1, 1, 1, 6, 1, 3, 1, 1, 1, 5, 2]
def baseStart_8171491 : Nat := 118140960795 + 8171491 * 2 ^ 59
def prefixEnd_8171491 : Nat := 4983230072969 + 3 ^ 40 * 8171491 * 2
def baseEnd_8171491 : Nat := 4195902546888993737582503

theorem tailTrace_8171491 : CollatzResearch.WordTrace tailWord_8171491 prefixEnd_8171491 4195902546888993737582503 := by
  unfold tailWord_8171491
  simp only [CollatzResearch.WordTrace]
  refine ⟨298038761639091161400146327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198692507759394107600097551 298038761639091161400146327)
  ·
    refine ⟨447058142458636742100219491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298038761639091161400146327 447058142458636742100219491)
    ·
      refine ⟨670587213687955113150329237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447058142458636742100219491 670587213687955113150329237)
      ·
        refine ⟨31433775641622895928921683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 670587213687955113150329237 31433775641622895928921683)
        ·
          refine ⟨47150663462434343893382525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31433775641622895928921683 47150663462434343893382525)
          ·
            refine ⟨17681498798412878960018447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47150663462434343893382525 17681498798412878960018447)
            ·
              refine ⟨26522248197619318440027671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17681498798412878960018447 26522248197619318440027671)
              ·
                refine ⟨39783372296428977660041507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26522248197619318440027671 39783372296428977660041507)
                ·
                  refine ⟨59675058444643466490062261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39783372296428977660041507 59675058444643466490062261)
                  ·
                    refine ⟨5594536729185324983443337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59675058444643466490062261 5594536729185324983443337)
                    ·
                      refine ⟨4195902546888993737582503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5594536729185324983443337 4195902546888993737582503)
                      ·
                        rfl

theorem cell23_8171491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_8171491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171491 prefixEnd_8171491 := by exact prefixLift 8171491
  have htrace : WordTrace (prefixWord ++ tailWord_8171491) baseStart_8171491 baseEnd_8171491 := by
    simpa [prefixWord, tailWord_8171491, baseEnd_8171491] using wordTrace_append hprefix tailTrace_8171491
  have hstable : (prefixWord ++ tailWord_8171491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171491).length < 2 ^ (prefixWord ++ tailWord_8171491).sum := by decide
  have hdescent : baseEnd_8171491 < baseStart_8171491 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171507 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 5]
def baseStart_8171507 : Nat := 118140960795 + 8171507 * 2 ^ 59
def prefixEnd_8171507 : Nat := 4983230072969 + 3 ^ 40 * 8171507 * 2
def baseEnd_8171507 : Nat := 4195910762579465674982429

theorem tailTrace_8171507 : CollatzResearch.WordTrace tailWord_8171507 prefixEnd_8171507 4195910762579465674982429 := by
  unfold tailWord_8171507
  simp only [CollatzResearch.WordTrace]
  refine ⟨298039345207033196132728775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198692896804688797421819183 298039345207033196132728775)
  ·
    refine ⟨447059017810549794199093163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298039345207033196132728775 447059017810549794199093163)
    ·
      refine ⟨670588526715824691298639745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447059017810549794199093163 670588526715824691298639745)
      ·
        refine ⟨502941395036868518473979809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 670588526715824691298639745 502941395036868518473979809)
        ·
          refine ⟨377206046277651388855484857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 502941395036868518473979809 377206046277651388855484857)
          ·
            refine ⟨282904534708238541641613643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377206046277651388855484857 282904534708238541641613643)
            ·
              refine ⟨424356802062357812462420465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282904534708238541641613643 424356802062357812462420465)
              ·
                refine ⟨318267601546768359346815349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 424356802062357812462420465 318267601546768359346815349)
                ·
                  refine ⟨29837587645009533688763939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 318267601546768359346815349 29837587645009533688763939)
                  ·
                    refine ⟨44756381467514300533145909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29837587645009533688763939 44756381467514300533145909)
                    ·
                      refine ⟨4195910762579465674982429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44756381467514300533145909 4195910762579465674982429)
                      ·
                        rfl

theorem cell23_8171507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 5].length) (baseStart_8171507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171507 prefixEnd_8171507 := by exact prefixLift 8171507
  have htrace : WordTrace (prefixWord ++ tailWord_8171507) baseStart_8171507 baseEnd_8171507 := by
    simpa [prefixWord, tailWord_8171507, baseEnd_8171507] using wordTrace_append hprefix tailTrace_8171507
  have hstable : (prefixWord ++ tailWord_8171507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171507).length < 2 ^ (prefixWord ++ tailWord_8171507).sum := by decide
  have hdescent : baseEnd_8171507 < baseStart_8171507 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171534 : List Nat := [4, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6]
def baseStart_8171534 : Nat := 118140960795 + 8171534 * 2 ^ 59
def prefixEnd_8171534 : Nat := 4983230072969 + 3 ^ 40 * 8171534 * 2
def baseEnd_8171534 : Nat := 4195924626557137069344805

theorem tailTrace_8171534 : CollatzResearch.WordTrace tailWord_8171534 prefixEnd_8171534 4195924626557137069344805 := by
  unfold tailWord_8171534
  simp only [CollatzResearch.WordTrace]
  refine ⟨37255041247241922467995207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198693553318623586495974437 37255041247241922467995207)
  ·
    refine ⟨55882561870862883701992811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37255041247241922467995207 55882561870862883701992811)
    ·
      refine ⟨83823842806294325552989217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55882561870862883701992811 83823842806294325552989217)
      ·
        refine ⟨62867882104720744164741913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83823842806294325552989217 62867882104720744164741913)
        ·
          refine ⟨47150911578540558123556435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62867882104720744164741913 47150911578540558123556435)
          ·
            refine ⟨70726367367810837185334653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47150911578540558123556435 70726367367810837185334653)
            ·
              refine ⟨26522387762929063944500495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70726367367810837185334653 26522387762929063944500495)
              ·
                refine ⟨39783581644393595916750743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26522387762929063944500495 39783581644393595916750743)
                ·
                  refine ⟨59675372466590393875126115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39783581644393595916750743 59675372466590393875126115)
                  ·
                    refine ⟨89513058699885590812689173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59675372466590393875126115 89513058699885590812689173)
                    ·
                      refine ⟨4195924626557137069344805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89513058699885590812689173 4195924626557137069344805)
                      ·
                        rfl

theorem cell23_8171534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_8171534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171534 prefixEnd_8171534 := by exact prefixLift 8171534
  have htrace : WordTrace (prefixWord ++ tailWord_8171534) baseStart_8171534 baseEnd_8171534 := by
    simpa [prefixWord, tailWord_8171534, baseEnd_8171534] using wordTrace_append hprefix tailTrace_8171534
  have hstable : (prefixWord ++ tailWord_8171534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171534).length < 2 ^ (prefixWord ++ tailWord_8171534).sum := by decide
  have hdescent : baseEnd_8171534 < baseStart_8171534 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171571 : List Nat := [1, 1, 1, 2, 4, 1, 4, 1, 4, 1, 3]
def baseStart_8171571 : Nat := 118140960795 + 8171571 * 2 ^ 59
def prefixEnd_8171571 : Nat := 4983230072969 + 3 ^ 40 * 8171571 * 2
def baseEnd_8171571 : Nat := 4195943625341353424582135

theorem tailTrace_8171571 : CollatzResearch.WordTrace tailWord_8171571 prefixEnd_8171571 4195943625341353424582135 := by
  unfold tailWord_8171571
  simp only [CollatzResearch.WordTrace]
  refine ⟨298041679478801335063058567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198694452985867556708705711 298041679478801335063058567)
  ·
    refine ⟨447062519218202002594587851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298041679478801335063058567 447062519218202002594587851)
    ·
      refine ⟨670593778827303003891881777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447062519218202002594587851 670593778827303003891881777)
      ·
        refine ⟨502945334120477252918911333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 670593778827303003891881777 502945334120477252918911333)
        ·
          refine ⟨94302250147589484922295875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 502945334120477252918911333 94302250147589484922295875)
          ·
            refine ⟨141453375221384227383443813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94302250147589484922295875 141453375221384227383443813)
            ·
              refine ⟨26522507854009542634395715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141453375221384227383443813 26522507854009542634395715)
              ·
                refine ⟨39783761781014313951593573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26522507854009542634395715 39783761781014313951593573)
                ·
                  refine ⟨7459455333940183865923795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39783761781014313951593573 7459455333940183865923795)
                  ·
                    refine ⟨11189183000910275798885693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7459455333940183865923795 11189183000910275798885693)
                    ·
                      refine ⟨4195943625341353424582135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11189183000910275798885693 4195943625341353424582135)
                      ·
                        rfl

theorem cell23_8171571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 4, 1, 3].length) (baseStart_8171571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171571 prefixEnd_8171571 := by exact prefixLift 8171571
  have htrace : WordTrace (prefixWord ++ tailWord_8171571) baseStart_8171571 baseEnd_8171571 := by
    simpa [prefixWord, tailWord_8171571, baseEnd_8171571] using wordTrace_append hprefix tailTrace_8171571
  have hstable : (prefixWord ++ tailWord_8171571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171571).length < 2 ^ (prefixWord ++ tailWord_8171571).sum := by decide
  have hdescent : baseEnd_8171571 < baseStart_8171571 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171582 : List Nat := [4, 2, 1, 3, 2, 2, 2, 1, 2, 4]
def baseStart_8171582 : Nat := 118140960795 + 8171582 * 2 ^ 59
def prefixEnd_8171582 : Nat := 4983230072969 + 3 ^ 40 * 8171582 * 2
def baseEnd_8171582 : Nat := 1398649757876184293848195

theorem tailTrace_8171582 : CollatzResearch.WordTrace tailWord_8171582 prefixEnd_8171582 1398649757876184293848195 := by
  unfold tailWord_8171582
  simp only [CollatzResearch.WordTrace]
  refine ⟨37255260085220185492713625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198694720454507655961139333 37255260085220185492713625)
  ·
    refine ⟨27941445063915139119535219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37255260085220185492713625 27941445063915139119535219)
    ·
      refine ⟨41912167595872708679302829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27941445063915139119535219 41912167595872708679302829)
      ·
        refine ⟨15717062848452265754738561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41912167595872708679302829 15717062848452265754738561)
        ·
          refine ⟨11787797136339199316053921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15717062848452265754738561 11787797136339199316053921)
          ·
            refine ⟨8840847852254399487040441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11787797136339199316053921 8840847852254399487040441)
            ·
              refine ⟨6630635889190799615280331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8840847852254399487040441 6630635889190799615280331)
              ·
                refine ⟨9945953833786199422920497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6630635889190799615280331 9945953833786199422920497)
                ·
                  refine ⟨7459465375339649567190373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9945953833786199422920497 7459465375339649567190373)
                  ·
                    refine ⟨1398649757876184293848195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7459465375339649567190373 1398649757876184293848195)
                    ·
                      rfl

theorem cell23_8171582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_8171582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171582 prefixEnd_8171582 := by exact prefixLift 8171582
  have htrace : WordTrace (prefixWord ++ tailWord_8171582) baseStart_8171582 baseEnd_8171582 := by
    simpa [prefixWord, tailWord_8171582, baseEnd_8171582] using wordTrace_append hprefix tailTrace_8171582
  have hstable : (prefixWord ++ tailWord_8171582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171582).length < 2 ^ (prefixWord ++ tailWord_8171582).sum := by decide
  have hdescent : baseEnd_8171582 < baseStart_8171582 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171598 : List Nat := [4, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2]
def baseStart_8171598 : Nat := 118140960795 + 8171598 * 2 ^ 59
def prefixEnd_8171598 : Nat := 4983230072969 + 3 ^ 40 * 8171598 * 2
def baseEnd_8171598 : Nat := 4195957489319024818944511

theorem tailTrace_8171598 : CollatzResearch.WordTrace tailWord_8171598 prefixEnd_8171598 4195957489319024818944511 := by
  unfold tailWord_8171598
  simp only [CollatzResearch.WordTrace]
  refine ⟨37255333031212939834286431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198695109499802345782860965 37255333031212939834286431)
  ·
    refine ⟨55882999546819409751429647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37255333031212939834286431 55882999546819409751429647)
    ·
      refine ⟨83824499320229114627144471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55882999546819409751429647 83824499320229114627144471)
      ·
        refine ⟨125736748980343671940716707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83824499320229114627144471 125736748980343671940716707)
        ·
          refine ⟨188605123470515507911075061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125736748980343671940716707 188605123470515507911075061)
          ·
            refine ⟨17681730325360828866663287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 188605123470515507911075061 17681730325360828866663287)
            ·
              refine ⟨26522595488041243299994931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17681730325360828866663287 26522595488041243299994931)
              ·
                refine ⟨39783893232061864949992397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26522595488041243299994931 39783893232061864949992397)
                ·
                  refine ⟨14918959962023199356247149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39783893232061864949992397 14918959962023199356247149)
                  ·
                    refine ⟨5594609985758699758592681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14918959962023199356247149 5594609985758699758592681)
                    ·
                      refine ⟨4195957489319024818944511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5594609985758699758592681 4195957489319024818944511)
                      ·
                        rfl

theorem cell23_8171598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2].length) (baseStart_8171598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171598 prefixEnd_8171598 := by exact prefixLift 8171598
  have htrace : WordTrace (prefixWord ++ tailWord_8171598) baseStart_8171598 baseEnd_8171598 := by
    simpa [prefixWord, tailWord_8171598, baseEnd_8171598] using wordTrace_append hprefix tailTrace_8171598
  have hstable : (prefixWord ++ tailWord_8171598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171598).length < 2 ^ (prefixWord ++ tailWord_8171598).sum := by decide
  have hdescent : baseEnd_8171598 < baseStart_8171598 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171604 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 4, 6]
def baseStart_8171604 : Nat := 118140960795 + 8171604 * 2 ^ 59
def prefixEnd_8171604 : Nat := 4983230072969 + 3 ^ 40 * 8171604 * 2
def baseEnd_8171604 : Nat := 1398653523400983931823161

theorem tailTrace_8171604 : CollatzResearch.WordTrace tailWord_8171604 prefixEnd_8171604 1398653523400983931823161 := by
  unfold tailWord_8171604
  simp only [CollatzResearch.WordTrace]
  refine ⟨149021441543840890849504933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198695255391787854466006577 149021441543840890849504933)
  ·
    refine ⟨27941520289470167034282175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149021441543840890849504933 27941520289470167034282175)
    ·
      refine ⟨41912280434205250551423263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27941520289470167034282175 41912280434205250551423263)
      ·
        refine ⟨62868420651307875827134895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41912280434205250551423263 62868420651307875827134895)
        ·
          refine ⟨94302630976961813740702343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62868420651307875827134895 94302630976961813740702343)
          ·
            refine ⟨141453946465442720611053515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94302630976961813740702343 141453946465442720611053515)
            ·
              refine ⟨212180919698164080916580273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141453946465442720611053515 212180919698164080916580273)
              ·
                refine ⟨159135689773623060687435205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212180919698164080916580273 159135689773623060687435205)
                ·
                  refine ⟨29837941832554323878894101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159135689773623060687435205 29837941832554323878894101)
                  ·
                    refine ⟨1398653523400983931823161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29837941832554323878894101 1398653523400983931823161)
                    ·
                      rfl

theorem cell23_8171604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_8171604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171604 prefixEnd_8171604 := by exact prefixLift 8171604
  have htrace : WordTrace (prefixWord ++ tailWord_8171604) baseStart_8171604 baseEnd_8171604 := by
    simpa [prefixWord, tailWord_8171604, baseEnd_8171604] using wordTrace_append hprefix tailTrace_8171604
  have hstable : (prefixWord ++ tailWord_8171604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171604).length < 2 ^ (prefixWord ++ tailWord_8171604).sum := by decide
  have hdescent : baseEnd_8171604 < baseStart_8171604 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171641 : List Nat := [1, 2, 1, 3, 4, 2, 1, 1, 2, 2, 4]
def baseStart_8171641 : Nat := 118140960795 + 8171641 * 2 ^ 59
def prefixEnd_8171641 : Nat := 4983230072969 + 3 ^ 40 * 8171641 * 2
def baseEnd_8171641 : Nat := 4195979568987168150706813

theorem tailTrace_8171641 : CollatzResearch.WordTrace tailWord_8171641 prefixEnd_8171641 4195979568987168150706813 := by
  unfold tailWord_8171641
  simp only [CollatzResearch.WordTrace]
  refine ⟨298044232588547737018106777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198696155059031824678737851 298044232588547737018106777)
  ·
    refine ⟨223533174441410802763580083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298044232588547737018106777 223533174441410802763580083)
    ·
      refine ⟨335299761662116204145370125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223533174441410802763580083 335299761662116204145370125)
      ·
        refine ⟨125737410623293576554513797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335299761662116204145370125 125737410623293576554513797)
        ·
          refine ⟨23575764491867545603971337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125737410623293576554513797 23575764491867545603971337)
          ·
            refine ⟨17681823368900659202978503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23575764491867545603971337 17681823368900659202978503)
            ·
              refine ⟨26522735053350988804467755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17681823368900659202978503 26522735053350988804467755)
              ·
                refine ⟨39784102580026483206701633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26522735053350988804467755 39784102580026483206701633)
                ·
                  refine ⟨29838076935019862405026225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39784102580026483206701633 29838076935019862405026225)
                  ·
                    refine ⟨22378557701264896803769669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29838076935019862405026225 22378557701264896803769669)
                    ·
                      refine ⟨4195979568987168150706813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22378557701264896803769669 4195979568987168150706813)
                      ·
                        rfl

theorem cell23_8171641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_8171641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171641 prefixEnd_8171641 := by exact prefixLift 8171641
  have htrace : WordTrace (prefixWord ++ tailWord_8171641) baseStart_8171641 baseEnd_8171641 := by
    simpa [prefixWord, tailWord_8171641, baseEnd_8171641] using wordTrace_append hprefix tailTrace_8171641
  have hstable : (prefixWord ++ tailWord_8171641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171641).length < 2 ^ (prefixWord ++ tailWord_8171641).sum := by decide
  have hdescent : baseEnd_8171641 < baseStart_8171641 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171645 : List Nat := [1, 4, 1, 1, 3, 2, 2, 3, 2, 2, 2]
def baseStart_8171645 : Nat := 118140960795 + 8171645 * 2 ^ 59
def prefixEnd_8171645 : Nat := 4983230072969 + 3 ^ 40 * 8171645 * 2
def baseEnd_8171645 : Nat := 4195981622909786135056795

theorem tailTrace_8171645 : CollatzResearch.WordTrace tailWord_8171645 prefixEnd_8171645 4195981622909786135056795 := by
  unfold tailWord_8171645
  simp only [CollatzResearch.WordTrace]
  refine ⟨298044378480533245701252389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198696252320355497134168259 298044378480533245701252389)
  ·
    refine ⟨55883320965099983568984823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298044378480533245701252389 55883320965099983568984823)
    ·
      refine ⟨83824981447649975353477235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55883320965099983568984823 83824981447649975353477235)
      ·
        refine ⟨125737472171474963030215853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83824981447649975353477235 125737472171474963030215853)
        ·
          refine ⟨47151552064303111136330945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125737472171474963030215853 47151552064303111136330945)
          ·
            refine ⟨35363664048227333352248209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47151552064303111136330945 35363664048227333352248209)
            ·
              refine ⟨26522748036170500014186157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35363664048227333352248209 26522748036170500014186157)
              ·
                refine ⟨9946030513563937505319809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26522748036170500014186157 9946030513563937505319809)
                ·
                  refine ⟨7459522885172953128989857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9946030513563937505319809 7459522885172953128989857)
                  ·
                    refine ⟨5594642163879714846742393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7459522885172953128989857 5594642163879714846742393)
                    ·
                      refine ⟨4195981622909786135056795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5594642163879714846742393 4195981622909786135056795)
                      ·
                        rfl

theorem cell23_8171645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3, 2, 2, 2].length) (baseStart_8171645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171645 prefixEnd_8171645 := by exact prefixLift 8171645
  have htrace : WordTrace (prefixWord ++ tailWord_8171645) baseStart_8171645 baseEnd_8171645 := by
    simpa [prefixWord, tailWord_8171645, baseEnd_8171645] using wordTrace_append hprefix tailTrace_8171645
  have hstable : (prefixWord ++ tailWord_8171645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171645).length < 2 ^ (prefixWord ++ tailWord_8171645).sum := by decide
  have hdescent : baseEnd_8171645 < baseStart_8171645 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171664 : List Nat := [2, 1, 1, 1, 1, 1, 7, 1, 1, 7]
def baseStart_8171664 : Nat := 118140960795 + 8171664 * 2 ^ 59
def prefixEnd_8171664 : Nat := 4983230072969 + 3 ^ 40 * 8171664 * 2
def baseEnd_8171664 : Nat := 1398663793014073853573069

theorem tailTrace_8171664 : CollatzResearch.WordTrace tailWord_8171664 prefixEnd_8171664 1398663793014073853573069 := by
  unfold tailWord_8171664
  simp only [CollatzResearch.WordTrace]
  refine ⟨149022535733732205973097023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198696714311642941297462697 149022535733732205973097023)
  ·
    refine ⟨223533803600598308959645535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149022535733732205973097023 223533803600598308959645535)
    ·
      refine ⟨335300705400897463439468303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223533803600598308959645535 335300705400897463439468303)
      ·
        refine ⟨502951058101346195159202455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335300705400897463439468303 502951058101346195159202455)
        ·
          refine ⟨754426587152019292738803683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502951058101346195159202455 754426587152019292738803683)
          ·
            refine ⟨1131639880728028939108205525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754426587152019292738803683 1131639880728028939108205525)
            ·
              refine ⟨26522809704563178260348567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1131639880728028939108205525 26522809704563178260348567)
              ·
                refine ⟨39784214556844767390522851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26522809704563178260348567 39784214556844767390522851)
                ·
                  refine ⟨59676321835267151085784277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39784214556844767390522851 59676321835267151085784277)
                  ·
                    refine ⟨1398663793014073853573069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59676321835267151085784277 1398663793014073853573069)
                    ·
                      rfl

theorem cell23_8171664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 1, 7].length) (baseStart_8171664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171664 prefixEnd_8171664 := by exact prefixLift 8171664
  have htrace : WordTrace (prefixWord ++ tailWord_8171664) baseStart_8171664 baseEnd_8171664 := by
    simpa [prefixWord, tailWord_8171664, baseEnd_8171664] using wordTrace_append hprefix tailTrace_8171664
  have hstable : (prefixWord ++ tailWord_8171664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171664).length < 2 ^ (prefixWord ++ tailWord_8171664).sum := by decide
  have hdescent : baseEnd_8171664 < baseStart_8171664 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171768 : List Nat := [2, 1, 2, 1, 1, 2, 1, 6, 3, 1, 3]
def baseStart_8171768 : Nat := 118140960795 + 8171768 * 2 ^ 59
def prefixEnd_8171768 : Nat := 4983230072969 + 3 ^ 40 * 8171768 * 2
def baseEnd_8171768 : Nat := 4196044781030289153818729

theorem tailTrace_8171768 : CollatzResearch.WordTrace tailWord_8171768 prefixEnd_8171768 4196044781030289153818729 := by
  unfold tailWord_8171768
  simp only [CollatzResearch.WordTrace]
  refine ⟨149024432329543818853989979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198699243106058425138653305 149024432329543818853989979)
  ·
    refine ⟨223536648494315728280984969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149024432329543818853989979 223536648494315728280984969)
    ·
      refine ⟨167652486370736796210738727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223536648494315728280984969 167652486370736796210738727)
      ·
        refine ⟨251478729556105194316108091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167652486370736796210738727 251478729556105194316108091)
        ·
          refine ⟨377218094334157791474162137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251478729556105194316108091 377218094334157791474162137)
          ·
            refine ⟨282913570750618343605621603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377218094334157791474162137 282913570750618343605621603)
            ·
              refine ⟨424370356125927515408432405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282913570750618343605621603 424370356125927515408432405)
              ·
                refine ⟨19892360443402852284770269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 424370356125927515408432405 19892360443402852284770269)
                ·
                  refine ⟨7459635166276069606788851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19892360443402852284770269 7459635166276069606788851)
                  ·
                    refine ⟨11189452749414104410183277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7459635166276069606788851 11189452749414104410183277)
                    ·
                      refine ⟨4196044781030289153818729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11189452749414104410183277 4196044781030289153818729)
                      ·
                        rfl

theorem cell23_8171768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 3, 1, 3].length) (baseStart_8171768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171768 prefixEnd_8171768 := by exact prefixLift 8171768
  have htrace : WordTrace (prefixWord ++ tailWord_8171768) baseStart_8171768 baseEnd_8171768 := by
    simpa [prefixWord, tailWord_8171768, baseEnd_8171768] using wordTrace_append hprefix tailTrace_8171768
  have hstable : (prefixWord ++ tailWord_8171768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171768).length < 2 ^ (prefixWord ++ tailWord_8171768).sum := by decide
  have hdescent : baseEnd_8171768 < baseStart_8171768 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171808 : List Nat := [2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 4]
def baseStart_8171808 : Nat := 118140960795 + 8171808 * 2 ^ 59
def prefixEnd_8171808 : Nat := 4983230072969 + 3 ^ 40 * 8171808 * 2
def baseEnd_8171808 : Nat := 4196065320256468997318545

theorem tailTrace_8171808 : CollatzResearch.WordTrace tailWord_8171808 prefixEnd_8171808 4196065320256468997318545 := by
  unfold tailWord_8171808
  simp only [CollatzResearch.WordTrace]
  refine ⟨149025161789471362269718039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198700215719295149692957385 149025161789471362269718039)
  ·
    refine ⟨223537742684207043404577059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149025161789471362269718039 223537742684207043404577059)
    ·
      refine ⟨335306614026310565106865589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223537742684207043404577059 335306614026310565106865589)
      ·
        refine ⟨31434995064966615478768649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 335306614026310565106865589 31434995064966615478768649)
        ·
          refine ⟨23576246298724961609076487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31434995064966615478768649 23576246298724961609076487)
          ·
            refine ⟨35364369448087442413614731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23576246298724961609076487 35364369448087442413614731)
            ·
              refine ⟨53046554172131163620422097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35364369448087442413614731 53046554172131163620422097)
              ·
                refine ⟨39784915629098372715316573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53046554172131163620422097 39784915629098372715316573)
                ·
                  refine ⟨14919343360911889768243715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39784915629098372715316573 14919343360911889768243715)
                  ·
                    refine ⟨22379015041367834652365573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14919343360911889768243715 22379015041367834652365573)
                    ·
                      refine ⟨4196065320256468997318545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22379015041367834652365573 4196065320256468997318545)
                      ·
                        rfl

theorem cell23_8171808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_8171808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171808 prefixEnd_8171808 := by exact prefixLift 8171808
  have htrace : WordTrace (prefixWord ++ tailWord_8171808) baseStart_8171808 baseEnd_8171808 := by
    simpa [prefixWord, tailWord_8171808, baseEnd_8171808] using wordTrace_append hprefix tailTrace_8171808
  have hstable : (prefixWord ++ tailWord_8171808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171808).length < 2 ^ (prefixWord ++ tailWord_8171808).sum := by decide
  have hdescent : baseEnd_8171808 < baseStart_8171808 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171811 : List Nat := [1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 5]
def baseStart_8171811 : Nat := 118140960795 + 8171811 * 2 ^ 59
def prefixEnd_8171811 : Nat := 4983230072969 + 3 ^ 40 * 8171811 * 2
def baseEnd_8171811 : Nat := 4196066860698432485581031

theorem tailTrace_8171811 : CollatzResearch.WordTrace tailWord_8171811 prefixEnd_8171811 4196066860698432485581031 := by
  unfold tailWord_8171811
  simp only [CollatzResearch.WordTrace]
  refine ⟨298050432997931856051795287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198700288665287904034530191 298050432997931856051795287)
  ·
    refine ⟨447075649496897784077692931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298050432997931856051795287 447075649496897784077692931)
    ·
      refine ⟨670613474245346676116539397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447075649496897784077692931 670613474245346676116539397)
      ·
        refine ⟨125740026421002501771851137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 670613474245346676116539397 125740026421002501771851137)
        ·
          refine ⟨94305019815751876328888353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125740026421002501771851137 94305019815751876328888353)
          ·
            refine ⟨70728764861813907246666265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94305019815751876328888353 70728764861813907246666265)
            ·
              refine ⟨53046573646360430434999699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70728764861813907246666265 53046573646360430434999699)
              ·
                refine ⟨79569860469540645652499549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53046573646360430434999699 79569860469540645652499549)
                ·
                  refine ⟨29838697676077742119687331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79569860469540645652499549 29838697676077742119687331)
                  ·
                    refine ⟨44758046514116613179530997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29838697676077742119687331 44758046514116613179530997)
                    ·
                      refine ⟨4196066860698432485581031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44758046514116613179530997 4196066860698432485581031)
                      ·
                        rfl

theorem cell23_8171811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_8171811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171811 prefixEnd_8171811 := by exact prefixLift 8171811
  have htrace : WordTrace (prefixWord ++ tailWord_8171811) baseStart_8171811 baseEnd_8171811 := by
    simpa [prefixWord, tailWord_8171811, baseEnd_8171811] using wordTrace_append hprefix tailTrace_8171811
  have hstable : (prefixWord ++ tailWord_8171811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171811).length < 2 ^ (prefixWord ++ tailWord_8171811).sum := by decide
  have hdescent : baseEnd_8171811 < baseStart_8171811 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171858 : List Nat := [3, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3]
def baseStart_8171858 : Nat := 118140960795 + 8171858 * 2 ^ 59
def prefixEnd_8171858 : Nat := 4983230072969 + 3 ^ 40 * 8171858 * 2
def baseEnd_8171858 : Nat := 4196090994289193801693315

theorem tailTrace_8171858 : CollatzResearch.WordTrace tailWord_8171858 prefixEnd_8171858 4196090994289193801693315 := by
  unfold tailWord_8171858
  simp only [CollatzResearch.WordTrace]
  refine ⟨74513036807190395769689057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198701431485841055385837485 74513036807190395769689057)
  ·
    refine ⟨55884777605392796827266793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74513036807190395769689057 55884777605392796827266793)
    ·
      refine ⟨41913583204044597620450095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55884777605392796827266793 41913583204044597620450095)
      ·
        refine ⟨62870374806066896430675143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41913583204044597620450095 62870374806066896430675143)
        ·
          refine ⟨94305562209100344646012715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62870374806066896430675143 94305562209100344646012715)
          ·
            refine ⟨141458343313650516969019073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94305562209100344646012715 141458343313650516969019073)
            ·
              refine ⟨106093757485237887726764305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141458343313650516969019073 106093757485237887726764305)
              ·
                refine ⟨79570318113928415795073229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106093757485237887726764305 79570318113928415795073229)
                ·
                  refine ⟨29838869292723155923152461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79570318113928415795073229 29838869292723155923152461)
                  ·
                    refine ⟨11189575984771183471182173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29838869292723155923152461 11189575984771183471182173)
                    ·
                      refine ⟨4196090994289193801693315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11189575984771183471182173 4196090994289193801693315)
                      ·
                        rfl

theorem cell23_8171858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_8171858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171858 prefixEnd_8171858 := by exact prefixLift 8171858
  have htrace : WordTrace (prefixWord ++ tailWord_8171858) baseStart_8171858 baseEnd_8171858 := by
    simpa [prefixWord, tailWord_8171858, baseEnd_8171858] using wordTrace_append hprefix tailTrace_8171858
  have hstable : (prefixWord ++ tailWord_8171858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171858).length < 2 ^ (prefixWord ++ tailWord_8171858).sum := by decide
  have hdescent : baseEnd_8171858 < baseStart_8171858 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171872 : List Nat := [2, 1, 1, 3, 6, 1, 1, 1, 1, 2, 4]
def baseStart_8171872 : Nat := 118140960795 + 8171872 * 2 ^ 59
def prefixEnd_8171872 : Nat := 4983230072969 + 3 ^ 40 * 8171872 * 2
def baseEnd_8171872 : Nat := 4196098183018356746918251

theorem tailTrace_8171872 : CollatzResearch.WordTrace tailWord_8171872 prefixEnd_8171872 4196098183018356746918251 := by
  unfold tailWord_8171872
  simp only [CollatzResearch.WordTrace]
  refine ⟨149026328925355431734882935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198701771900473908979843913 149026328925355431734882935)
  ·
    refine ⟨223539493388033147602324403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149026328925355431734882935 223539493388033147602324403)
    ·
      refine ⟨335309240082049721403486605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223539493388033147602324403 335309240082049721403486605)
      ·
        refine ⟨125740965030768645526307477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335309240082049721403486605 125740965030768645526307477)
        ·
          refine ⟨5894107735817280259045663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 125740965030768645526307477 5894107735817280259045663)
          ·
            refine ⟨8841161603725920388568495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5894107735817280259045663 8841161603725920388568495)
            ·
              refine ⟨13261742405588880582852743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8841161603725920388568495 13261742405588880582852743)
              ·
                refine ⟨19892613608383320874279115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13261742405588880582852743 19892613608383320874279115)
                ·
                  refine ⟨29838920412574981311418673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19892613608383320874279115 29838920412574981311418673)
                  ·
                    refine ⟨22379190309431235983564005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29838920412574981311418673 22379190309431235983564005)
                    ·
                      refine ⟨4196098183018356746918251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22379190309431235983564005 4196098183018356746918251)
                      ·
                        rfl

theorem cell23_8171872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 1, 2, 4].length) (baseStart_8171872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171872 prefixEnd_8171872 := by exact prefixLift 8171872
  have htrace : WordTrace (prefixWord ++ tailWord_8171872) baseStart_8171872 baseEnd_8171872 := by
    simpa [prefixWord, tailWord_8171872, baseEnd_8171872] using wordTrace_append hprefix tailTrace_8171872
  have hstable : (prefixWord ++ tailWord_8171872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171872).length < 2 ^ (prefixWord ++ tailWord_8171872).sum := by decide
  have hdescent : baseEnd_8171872 < baseStart_8171872 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171938 : List Nat := [3, 3, 1, 2, 1, 1, 2, 1, 9]
def baseStart_8171938 : Nat := 118140960795 + 8171938 * 2 ^ 59
def prefixEnd_8171938 : Nat := 4983230072969 + 3 ^ 40 * 8171938 * 2
def baseEnd_8171938 : Nat := 466236896971283720965883

theorem tailTrace_8171938 : CollatzResearch.WordTrace tailWord_8171938 prefixEnd_8171938 466236896971283720965883 := by
  unfold tailWord_8171938
  simp only [CollatzResearch.WordTrace]
  refine ⟨74513766267117939185417117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198703376712314504494445645 74513766267117939185417117)
  ·
    refine ⟨27942662350169227194531419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74513766267117939185417117 27942662350169227194531419)
    ·
      refine ⟨41913993525253840791797129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27942662350169227194531419 41913993525253840791797129)
      ·
        refine ⟨31435495143940380593847847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41913993525253840791797129 31435495143940380593847847)
        ·
          refine ⟨47153242715910570890771771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31435495143940380593847847 47153242715910570890771771)
          ·
            refine ⟨70729864073865856336157657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47153242715910570890771771 70729864073865856336157657)
            ·
              refine ⟨53047398055399392252118243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70729864073865856336157657 53047398055399392252118243)
              ·
                refine ⟨79571097083099088378177365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53047398055399392252118243 79571097083099088378177365)
                ·
                  refine ⟨466236896971283720965883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 79571097083099088378177365 466236896971283720965883)
                  ·
                    rfl

theorem cell23_8171938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_8171938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171938 prefixEnd_8171938 := by exact prefixLift 8171938
  have htrace : WordTrace (prefixWord ++ tailWord_8171938) baseStart_8171938 baseEnd_8171938 := by
    simpa [prefixWord, tailWord_8171938, baseEnd_8171938] using wordTrace_append hprefix tailTrace_8171938
  have hstable : (prefixWord ++ tailWord_8171938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171938).length < 2 ^ (prefixWord ++ tailWord_8171938).sum := by decide
  have hdescent : baseEnd_8171938 < baseStart_8171938 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171948 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 3]
def baseStart_8171948 : Nat := 118140960795 + 8171948 * 2 ^ 59
def prefixEnd_8171948 : Nat := 4983230072969 + 3 ^ 40 * 8171948 * 2
def baseEnd_8171948 : Nat := 4196137207548098449567901

theorem tailTrace_8171948 : CollatzResearch.WordTrace tailWord_8171948 prefixEnd_8171948 4196137207548098449567901 := by
  unfold tailWord_8171948
  simp only [CollatzResearch.WordTrace]
  refine ⟨149027714899217764224766249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198703619865623685633021665 149027714899217764224766249)
  ·
    refine ⟨111770786174413323168574687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149027714899217764224766249 111770786174413323168574687)
    ·
      refine ⟨167656179261619984752862031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111770786174413323168574687 167656179261619984752862031)
      ·
        refine ⟨251484268892429977129293047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167656179261619984752862031 251484268892429977129293047)
        ·
          refine ⟨377226403338644965693939571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251484268892429977129293047 377226403338644965693939571)
          ·
            refine ⟨565839605007967448540909357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377226403338644965693939571 565839605007967448540909357)
            ·
              refine ⟨212189851877987793202841009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 565839605007967448540909357 212189851877987793202841009)
              ·
                refine ⟨159142388908490844902130757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212189851877987793202841009 159142388908490844902130757)
                ·
                  refine ⟨29839197920342033419149517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159142388908490844902130757 29839197920342033419149517)
                  ·
                    refine ⟨11189699220128262532181069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29839197920342033419149517 11189699220128262532181069)
                    ·
                      refine ⟨4196137207548098449567901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11189699220128262532181069 4196137207548098449567901)
                      ·
                        rfl

theorem cell23_8171948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 3].length) (baseStart_8171948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171948 prefixEnd_8171948 := by exact prefixLift 8171948
  have htrace : WordTrace (prefixWord ++ tailWord_8171948) baseStart_8171948 baseEnd_8171948 := by
    simpa [prefixWord, tailWord_8171948, baseEnd_8171948] using wordTrace_append hprefix tailTrace_8171948
  have hstable : (prefixWord ++ tailWord_8171948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171948).length < 2 ^ (prefixWord ++ tailWord_8171948).sum := by decide
  have hdescent : baseEnd_8171948 < baseStart_8171948 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171949 : List Nat := [1, 5, 2, 2, 2, 1, 1, 2, 1, 4, 2]
def baseStart_8171949 : Nat := 118140960795 + 8171949 * 2 ^ 59
def prefixEnd_8171949 : Nat := 4983230072969 + 3 ^ 40 * 8171949 * 2
def baseEnd_8171949 : Nat := 4196137721028752945655397

theorem tailTrace_8171949 : CollatzResearch.WordTrace tailWord_8171949 prefixEnd_8171949 4196137721028752945655397 := by
  unfold tailWord_8171949
  simp only [CollatzResearch.WordTrace]
  refine ⟨298055466271431905620318901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198703644180954603746879267 298055466271431905620318901)
  ·
    refine ⟨27942699962946741151904897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 298055466271431905620318901 27942699962946741151904897)
    ·
      refine ⟨20957024972210055863928673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27942699962946741151904897 20957024972210055863928673)
      ·
        refine ⟨15717768729157541897946505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20957024972210055863928673 15717768729157541897946505)
        ·
          refine ⟨11788326546868156423459879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15717768729157541897946505 11788326546868156423459879)
          ·
            refine ⟨17682489820302234635189819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11788326546868156423459879 17682489820302234635189819)
            ·
              refine ⟨26523734730453351952784729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17682489820302234635189819 26523734730453351952784729)
              ·
                refine ⟨19892801047840013964588547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26523734730453351952784729 19892801047840013964588547)
                ·
                  refine ⟨29839201571760020946882821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19892801047840013964588547 29839201571760020946882821)
                  ·
                    refine ⟨5594850294705003927540529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29839201571760020946882821 5594850294705003927540529)
                    ·
                      refine ⟨4196137721028752945655397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5594850294705003927540529 4196137721028752945655397)
                      ·
                        rfl

theorem cell23_8171949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_8171949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171949 prefixEnd_8171949 := by exact prefixLift 8171949
  have htrace : WordTrace (prefixWord ++ tailWord_8171949) baseStart_8171949 baseEnd_8171949 := by
    simpa [prefixWord, tailWord_8171949, baseEnd_8171949] using wordTrace_append hprefix tailTrace_8171949
  have hstable : (prefixWord ++ tailWord_8171949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171949).length < 2 ^ (prefixWord ++ tailWord_8171949).sum := by decide
  have hdescent : baseEnd_8171949 < baseStart_8171949 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171975 : List Nat := [1, 1, 4, 1, 1, 4, 1, 1, 2, 5, 2]
def baseStart_8171975 : Nat := 118140960795 + 8171975 * 2 ^ 59
def prefixEnd_8171975 : Nat := 4983230072969 + 3 ^ 40 * 8171975 * 2
def baseEnd_8171975 : Nat := 4196151071525769843930277

theorem tailTrace_8171975 : CollatzResearch.WordTrace tailWord_8171975 prefixEnd_8171975 4196151071525769843930277 := by
  unfold tailWord_8171975
  simp only [CollatzResearch.WordTrace]
  refine ⟨298056414569337712060765379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198704276379558474707176919 298056414569337712060765379)
  ·
    refine ⟨447084621854006568091148069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298056414569337712060765379 447084621854006568091148069)
    ·
      refine ⟨83828366597626231517090263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 447084621854006568091148069 83828366597626231517090263)
      ·
        refine ⟨125742549896439347275635395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83828366597626231517090263 125742549896439347275635395)
        ·
          refine ⟨188613824844659020913453093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125742549896439347275635395 188613824844659020913453093)
          ·
            refine ⟨35365092158373566421272455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188613824844659020913453093 35365092158373566421272455)
            ·
              refine ⟨53047638237560349631908683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35365092158373566421272455 53047638237560349631908683)
              ·
                refine ⟨79571457356340524447863025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53047638237560349631908683 79571457356340524447863025)
                ·
                  refine ⟨59678593017255393335897269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79571457356340524447863025 59678593017255393335897269)
                  ·
                    refine ⟨5594868095367693125240369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59678593017255393335897269 5594868095367693125240369)
                    ·
                      refine ⟨4196151071525769843930277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5594868095367693125240369 4196151071525769843930277)
                      ·
                        rfl

theorem cell23_8171975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 5, 2].length) (baseStart_8171975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171975 prefixEnd_8171975 := by exact prefixLift 8171975
  have htrace : WordTrace (prefixWord ++ tailWord_8171975) baseStart_8171975 baseEnd_8171975 := by
    simpa [prefixWord, tailWord_8171975, baseEnd_8171975] using wordTrace_append hprefix tailTrace_8171975
  have hstable : (prefixWord ++ tailWord_8171975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171975).length < 2 ^ (prefixWord ++ tailWord_8171975).sum := by decide
  have hdescent : baseEnd_8171975 < baseStart_8171975 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8171978 : List Nat := [3, 1, 2, 1, 2, 2, 1, 3, 1, 2, 5]
def baseStart_8171978 : Nat := 118140960795 + 8171978 * 2 ^ 59
def prefixEnd_8171978 : Nat := 4983230072969 + 3 ^ 40 * 8171978 * 2
def baseEnd_8171978 : Nat := 4196152611967733332192763

theorem tailTrace_8171978 : CollatzResearch.WordTrace tailWord_8171978 prefixEnd_8171978 4196152611967733332192763 := by
  unfold tailWord_8171978
  simp only [CollatzResearch.WordTrace]
  refine ⟨74514130997081710893281147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198704349325551229048749725 74514130997081710893281147)
  ·
    refine ⟨111771196495622566339921721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74514130997081710893281147 111771196495622566339921721)
    ·
      refine ⟨83828397371716924754941291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111771196495622566339921721 83828397371716924754941291)
      ·
        refine ⟨125742596057575387132411937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83828397371716924754941291 125742596057575387132411937)
        ·
          refine ⟨94306947043181540349308953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125742596057575387132411937 94306947043181540349308953)
          ·
            refine ⟨70730210282386155261981715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94306947043181540349308953 70730210282386155261981715)
            ·
              refine ⟨106095315423579232892972573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70730210282386155261981715 106095315423579232892972573)
              ·
                refine ⟨39785743283842212334864715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106095315423579232892972573 39785743283842212334864715)
                ·
                  refine ⟨59678614925763318502297073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39785743283842212334864715 59678614925763318502297073)
                  ·
                    refine ⟨44758961194322488876722805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59678614925763318502297073 44758961194322488876722805)
                    ·
                      refine ⟨4196152611967733332192763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44758961194322488876722805 4196152611967733332192763)
                      ·
                        rfl

theorem cell23_8171978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_8171978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8171978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8171978 prefixEnd_8171978 := by exact prefixLift 8171978
  have htrace : WordTrace (prefixWord ++ tailWord_8171978) baseStart_8171978 baseEnd_8171978 := by
    simpa [prefixWord, tailWord_8171978, baseEnd_8171978] using wordTrace_append hprefix tailTrace_8171978
  have hstable : (prefixWord ++ tailWord_8171978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8171978).length < 2 ^ (prefixWord ++ tailWord_8171978).sum := by decide
  have hdescent : baseEnd_8171978 < baseStart_8171978 := by decide
  rcases family_descends (prefixWord ++ tailWord_8171978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172022 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2]
def baseStart_8172022 : Nat := 118140960795 + 8172022 * 2 ^ 59
def prefixEnd_8172022 : Nat := 4983230072969 + 3 ^ 40 * 8172022 * 2
def baseEnd_8172022 : Nat := 4196175205116531160042561

theorem tailTrace_8172022 : CollatzResearch.WordTrace tailWord_8172022 prefixEnd_8172022 4196175205116531160042561 := by
  unfold tailWord_8172022
  simp only [CollatzResearch.WordTrace]
  refine ⟨18628633050010464942982895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198705419200111626058484213 18628633050010464942982895)
  ·
    refine ⟨27942949575015697414474343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18628633050010464942982895 27942949575015697414474343)
    ·
      refine ⟨41914424362523546121711515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27942949575015697414474343 41914424362523546121711515)
      ·
        refine ⟨62871636543785319182567273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41914424362523546121711515 62871636543785319182567273)
        ·
          refine ⟨47153727407838989386925455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62871636543785319182567273 47153727407838989386925455)
          ·
            refine ⟨70730591111758484080388183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47153727407838989386925455 70730591111758484080388183)
            ·
              refine ⟨106095886667637726120582275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70730591111758484080388183 106095886667637726120582275)
              ·
                refine ⟨159143830001456589180873413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106095886667637726120582275 159143830001456589180873413)
                ·
                  refine ⟨29839468125273110471413765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159143830001456589180873413 29839468125273110471413765)
                  ·
                    refine ⟨5594900273488708213390081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29839468125273110471413765 5594900273488708213390081)
                    ·
                      refine ⟨4196175205116531160042561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5594900273488708213390081 4196175205116531160042561)
                      ·
                        rfl

theorem cell23_8172022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2].length) (baseStart_8172022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172022 prefixEnd_8172022 := by exact prefixLift 8172022
  have htrace : WordTrace (prefixWord ++ tailWord_8172022) baseStart_8172022 baseEnd_8172022 := by
    simpa [prefixWord, tailWord_8172022, baseEnd_8172022] using wordTrace_append hprefix tailTrace_8172022
  have hstable : (prefixWord ++ tailWord_8172022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172022).length < 2 ^ (prefixWord ++ tailWord_8172022).sum := by decide
  have hdescent : baseEnd_8172022 < baseStart_8172022 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172025 : List Nat := [1, 2, 1, 3, 1, 2, 2, 4, 2, 2, 3]
def baseStart_8172025 : Nat := 118140960795 + 8172025 * 2 ^ 59
def prefixEnd_8172025 : Nat := 4983230072969 + 3 ^ 40 * 8172025 * 2
def baseEnd_8172025 : Nat := 4196176745558494648305047

theorem tailTrace_8172025 : CollatzResearch.WordTrace tailWord_8172025 prefixEnd_8172025 4196176745558494648305047 := by
  unfold tailWord_8172025
  simp only [CollatzResearch.WordTrace]
  refine ⟨298058238219156570600085529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198705492146104380400057019 298058238219156570600085529)
  ·
    refine ⟨223543678664367427950064147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298058238219156570600085529 223543678664367427950064147)
    ·
      refine ⟨335315517996551141925096221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223543678664367427950064147 335315517996551141925096221)
      ·
        refine ⟨125743319248706678221911083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335315517996551141925096221 125743319248706678221911083)
        ·
          refine ⟨188614978873060017332866625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125743319248706678221911083 188614978873060017332866625)
          ·
            refine ⟨141461234154795012999649969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188614978873060017332866625 141461234154795012999649969)
            ·
              refine ⟨106095925616096259749737477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141461234154795012999649969 106095925616096259749737477)
              ·
                refine ⟨19892986053018048703075777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106095925616096259749737477 19892986053018048703075777)
                ·
                  refine ⟨14919739539763536527306833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19892986053018048703075777 14919739539763536527306833)
                  ·
                    refine ⟨11189804654822652395480125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14919739539763536527306833 11189804654822652395480125)
                    ·
                      refine ⟨4196176745558494648305047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11189804654822652395480125 4196176745558494648305047)
                      ·
                        rfl

theorem cell23_8172025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2, 2, 3].length) (baseStart_8172025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172025 prefixEnd_8172025 := by exact prefixLift 8172025
  have htrace : WordTrace (prefixWord ++ tailWord_8172025) baseStart_8172025 baseEnd_8172025 := by
    simpa [prefixWord, tailWord_8172025, baseEnd_8172025] using wordTrace_append hprefix tailTrace_8172025
  have hstable : (prefixWord ++ tailWord_8172025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172025).length < 2 ^ (prefixWord ++ tailWord_8172025).sum := by decide
  have hdescent : baseEnd_8172025 < baseStart_8172025 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172082 : List Nat := [3, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2]
def baseStart_8172082 : Nat := 118140960795 + 8172082 * 2 ^ 59
def prefixEnd_8172082 : Nat := 4983230072969 + 3 ^ 40 * 8172082 * 2
def baseEnd_8172082 : Nat := 4196206013955800925292285

theorem tailTrace_8172082 : CollatzResearch.WordTrace tailWord_8172082 prefixEnd_8172082 4196206013955800925292285 := by
  unfold tailWord_8172082
  simp only [CollatzResearch.WordTrace]
  refine ⟨74515079294987517333727625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198706878119966712889940333 74515079294987517333727625)
  ·
    refine ⟨55886309471240638000295719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74515079294987517333727625 55886309471240638000295719)
    ·
      refine ⟨83829464206860957000443579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55886309471240638000295719 83829464206860957000443579)
      ·
        refine ⟨125744196310291435500665369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83829464206860957000443579 125744196310291435500665369)
        ·
          refine ⟨94308147232718576625499027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125744196310291435500665369 94308147232718576625499027)
          ·
            refine ⟨141462220849077864938248541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94308147232718576625499027 141462220849077864938248541)
            ·
              refine ⟨53048332818404199351843203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141462220849077864938248541 53048332818404199351843203)
              ·
                refine ⟨79572499227606299027764805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53048332818404199351843203 79572499227606299027764805)
                ·
                  refine ⟨14919843605176181067705901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79572499227606299027764805 14919843605176181067705901)
                  ·
                    refine ⟨5594941351941067900389713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14919843605176181067705901 5594941351941067900389713)
                    ·
                      refine ⟨4196206013955800925292285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5594941351941067900389713 4196206013955800925292285)
                      ·
                        rfl

theorem cell23_8172082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2].length) (baseStart_8172082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172082 prefixEnd_8172082 := by exact prefixLift 8172082
  have htrace : WordTrace (prefixWord ++ tailWord_8172082) baseStart_8172082 baseEnd_8172082 := by
    simpa [prefixWord, tailWord_8172082, baseEnd_8172082] using wordTrace_append hprefix tailTrace_8172082
  have hstable : (prefixWord ++ tailWord_8172082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172082).length < 2 ^ (prefixWord ++ tailWord_8172082).sum := by decide
  have hdescent : baseEnd_8172082 < baseStart_8172082 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172095 : List Nat := [1, 1, 2, 2, 3, 2, 2, 2, 3, 1, 4]
def baseStart_8172095 : Nat := 118140960795 + 8172095 * 2 ^ 59
def prefixEnd_8172095 : Nat := 4983230072969 + 3 ^ 40 * 8172095 * 2
def baseEnd_8172095 : Nat := 4196212689204309374429725

theorem tailTrace_8172095 : CollatzResearch.WordTrace tailWord_8172095 prefixEnd_8172095 4196212689204309374429725 := by
  unfold tailWord_8172095
  simp only [CollatzResearch.WordTrace]
  refine ⟨298060791328902972555133739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198707194219268648370089159 298060791328902972555133739)
  ·
    refine ⟨447091186993354458832700609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298060791328902972555133739 447091186993354458832700609)
    ·
      refine ⟨335318390245015844124525457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447091186993354458832700609 335318390245015844124525457)
      ·
        refine ⟨251488792683761883093394093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335318390245015844124525457 251488792683761883093394093)
        ·
          refine ⟨94308297256410706160022785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251488792683761883093394093 94308297256410706160022785)
          ·
            refine ⟨70731222942308029620017089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94308297256410706160022785 70731222942308029620017089)
            ·
              refine ⟨53048417206731022215012817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70731222942308029620017089 53048417206731022215012817)
              ·
                refine ⟨39786312905048266661259613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53048417206731022215012817 39786312905048266661259613)
                ·
                  refine ⟨14919867339393099997972355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39786312905048266661259613 14919867339393099997972355)
                  ·
                    refine ⟨22379801009089649996958533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14919867339393099997972355 22379801009089649996958533)
                    ·
                      refine ⟨4196212689204309374429725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22379801009089649996958533 4196212689204309374429725)
                      ·
                        rfl

theorem cell23_8172095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3, 1, 4].length) (baseStart_8172095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172095 prefixEnd_8172095 := by exact prefixLift 8172095
  have htrace : WordTrace (prefixWord ++ tailWord_8172095) baseStart_8172095 baseEnd_8172095 := by
    simpa [prefixWord, tailWord_8172095, baseEnd_8172095] using wordTrace_append hprefix tailTrace_8172095
  have hstable : (prefixWord ++ tailWord_8172095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172095).length < 2 ^ (prefixWord ++ tailWord_8172095).sum := by decide
  have hdescent : baseEnd_8172095 < baseStart_8172095 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172109 : List Nat := [1, 6, 1, 1, 2, 1, 3, 2, 1, 5]
def baseStart_8172109 : Nat := 118140960795 + 8172109 * 2 ^ 59
def prefixEnd_8172109 : Nat := 4983230072969 + 3 ^ 40 * 8172109 * 2
def baseEnd_8172109 : Nat := 1398739959311157439884887

theorem tailTrace_8172109 : CollatzResearch.WordTrace tailWord_8172109 prefixEnd_8172109 1398739959311157439884887 := by
  unfold tailWord_8172109
  simp only [CollatzResearch.WordTrace]
  refine ⟨298061301950852252946143381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198707534633901501964095587 298061301950852252946143381)
  ·
    refine ⟨13971623528946199356850471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 298061301950852252946143381 13971623528946199356850471)
    ·
      refine ⟨20957435293419299035275707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13971623528946199356850471 20957435293419299035275707)
      ·
        refine ⟨31436152940128948552913561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20957435293419299035275707 31436152940128948552913561)
        ·
          refine ⟨23577114705096711414685171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31436152940128948552913561 23577114705096711414685171)
          ·
            refine ⟨35365672057645067122027757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23577114705096711414685171 35365672057645067122027757)
            ·
              refine ⟨13262127021616900170760409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35365672057645067122027757 13262127021616900170760409)
              ·
                refine ⟨9946595266212675128070307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13262127021616900170760409 9946595266212675128070307)
                ·
                  refine ⟨14919892899319012692105461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9946595266212675128070307 14919892899319012692105461)
                  ·
                    refine ⟨1398739959311157439884887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14919892899319012692105461 1398739959311157439884887)
                    ·
                      rfl

theorem cell23_8172109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_8172109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172109 prefixEnd_8172109 := by exact prefixLift 8172109
  have htrace : WordTrace (prefixWord ++ tailWord_8172109) baseStart_8172109 baseEnd_8172109 := by
    simpa [prefixWord, tailWord_8172109, baseEnd_8172109] using wordTrace_append hprefix tailTrace_8172109
  have hstable : (prefixWord ++ tailWord_8172109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172109).length < 2 ^ (prefixWord ++ tailWord_8172109).sum := by decide
  have hdescent : baseEnd_8172109 < baseStart_8172109 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172129 : List Nat := [1, 2, 3, 1, 1, 5, 3, 1, 1, 1, 4]
def baseStart_8172129 : Nat := 118140960795 + 8172129 * 2 ^ 59
def prefixEnd_8172129 : Nat := 4983230072969 + 3 ^ 40 * 8172129 * 2
def baseEnd_8172129 : Nat := 4196230147546562241404569

theorem tailTrace_8172129 : CollatzResearch.WordTrace tailWord_8172129 prefixEnd_8172129 4196230147546562241404569 := by
  unfold tailWord_8172129
  simp only [CollatzResearch.WordTrace]
  refine ⟨298062031410779796361871441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198708020940519864241247627 298062031410779796361871441)
  ·
    refine ⟨223546523558084847271403581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298062031410779796361871441 223546523558084847271403581)
    ·
      refine ⟨83829946334281817726776343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223546523558084847271403581 83829946334281817726776343)
      ·
        refine ⟨125744919501422726590164515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83829946334281817726776343 125744919501422726590164515)
        ·
          refine ⟨188617379252134089885246773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125744919501422726590164515 188617379252134089885246773)
          ·
            refine ⟨17682879304887570926741885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 188617379252134089885246773 17682879304887570926741885)
            ·
              refine ⟨6631079739332839097528207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17682879304887570926741885 6631079739332839097528207)
              ·
                refine ⟨9946619608999258646292311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6631079739332839097528207 9946619608999258646292311)
                ·
                  refine ⟨14919929413498887969438467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9946619608999258646292311 14919929413498887969438467)
                  ·
                    refine ⟨22379894120248331954157701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14919929413498887969438467 22379894120248331954157701)
                    ·
                      refine ⟨4196230147546562241404569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22379894120248331954157701 4196230147546562241404569)
                      ·
                        rfl

theorem cell23_8172129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 1, 1, 1, 4].length) (baseStart_8172129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172129 prefixEnd_8172129 := by exact prefixLift 8172129
  have htrace : WordTrace (prefixWord ++ tailWord_8172129) baseStart_8172129 baseEnd_8172129 := by
    simpa [prefixWord, tailWord_8172129, baseEnd_8172129] using wordTrace_append hprefix tailTrace_8172129
  have hstable : (prefixWord ++ tailWord_8172129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172129).length < 2 ^ (prefixWord ++ tailWord_8172129).sum := by decide
  have hdescent : baseEnd_8172129 < baseStart_8172129 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172180 : List Nat := [2, 4, 2, 2, 1, 2, 2, 3, 1, 2, 2]
def baseStart_8172180 : Nat := 118140960795 + 8172180 * 2 ^ 59
def prefixEnd_8172180 : Nat := 4983230072969 + 3 ^ 40 * 8172180 * 2
def baseEnd_8172180 : Nat := 4196256335059941541866835

theorem tailTrace_8172180 : CollatzResearch.WordTrace tailWord_8172180 prefixEnd_8172180 4196256335059941541866835 := by
  unfold tailWord_8172180
  simp only [CollatzResearch.WordTrace]
  refine ⟨149031945766797516035988997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198709261022396688047985329 149031945766797516035988997)
  ·
    refine ⟨27943489831274534256747937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149031945766797516035988997 27943489831274534256747937)
    ·
      refine ⟨20957617373455900692560953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27943489831274534256747937 20957617373455900692560953)
      ·
        refine ⟨15718213030091925519420715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20957617373455900692560953 15718213030091925519420715)
        ·
          refine ⟨23577319545137888279131073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15718213030091925519420715 23577319545137888279131073)
          ·
            refine ⟨17682989658853416209348305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23577319545137888279131073 17682989658853416209348305)
            ·
              refine ⟨13262242244140062157011229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17682989658853416209348305 13262242244140062157011229)
              ·
                refine ⟨4973340841552523308879211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13262242244140062157011229 4973340841552523308879211)
                ·
                  refine ⟨7460011262328784963318817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4973340841552523308879211 7460011262328784963318817)
                  ·
                    refine ⟨5595008446746588722489113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7460011262328784963318817 5595008446746588722489113)
                    ·
                      refine ⟨4196256335059941541866835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5595008446746588722489113 4196256335059941541866835)
                      ·
                        rfl

theorem cell23_8172180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_8172180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172180 prefixEnd_8172180 := by exact prefixLift 8172180
  have htrace : WordTrace (prefixWord ++ tailWord_8172180) baseStart_8172180 baseEnd_8172180 := by
    simpa [prefixWord, tailWord_8172180, baseEnd_8172180] using wordTrace_append hprefix tailTrace_8172180
  have hstable : (prefixWord ++ tailWord_8172180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172180).length < 2 ^ (prefixWord ++ tailWord_8172180).sum := by decide
  have hdescent : baseEnd_8172180 < baseStart_8172180 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172213 : List Nat := [1, 3, 3, 3, 1, 2, 3, 1, 2, 1, 3]
def baseStart_8172213 : Nat := 118140960795 + 8172213 * 2 ^ 59
def prefixEnd_8172213 : Nat := 4983230072969 + 3 ^ 40 * 8172213 * 2
def baseEnd_8172213 : Nat := 4196273279921539912754183

theorem tailTrace_8172213 : CollatzResearch.WordTrace tailWord_8172213 prefixEnd_8172213 4196273279921539912754183 := by
  unfold tailWord_8172213
  simp only [CollatzResearch.WordTrace]
  refine ⟨298065095142475478707929293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198710063428316985805286195 298065095142475478707929293)
  ·
    refine ⟨111774410678428304515473485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298065095142475478707929293 111774410678428304515473485)
    ·
      refine ⟨41915404004410614193302557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111774410678428304515473485 41915404004410614193302557)
      ·
        refine ⟨15718276501653980322488459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41915404004410614193302557 15718276501653980322488459)
        ·
          refine ⟨23577414752480970483732689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15718276501653980322488459 23577414752480970483732689)
          ·
            refine ⟨17683061064360727862799517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23577414752480970483732689 17683061064360727862799517)
            ·
              refine ⟨6631147899135272948549819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17683061064360727862799517 6631147899135272948549819)
              ·
                refine ⟨9946721848702909422824729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6631147899135272948549819 9946721848702909422824729)
                ·
                  refine ⟨7460041386527182067118547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9946721848702909422824729 7460041386527182067118547)
                  ·
                    refine ⟨11190062079790773100677821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7460041386527182067118547 11190062079790773100677821)
                    ·
                      refine ⟨4196273279921539912754183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11190062079790773100677821 4196273279921539912754183)
                      ·
                        rfl

theorem cell23_8172213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_8172213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172213 prefixEnd_8172213 := by exact prefixLift 8172213
  have htrace : WordTrace (prefixWord ++ tailWord_8172213) baseStart_8172213 baseEnd_8172213 := by
    simpa [prefixWord, tailWord_8172213, baseEnd_8172213] using wordTrace_append hprefix tailTrace_8172213
  have hstable : (prefixWord ++ tailWord_8172213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172213).length < 2 ^ (prefixWord ++ tailWord_8172213).sum := by decide
  have hdescent : baseEnd_8172213 < baseStart_8172213 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172222 : List Nat := [4, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5]
def baseStart_8172222 : Nat := 118140960795 + 8172222 * 2 ^ 59
def prefixEnd_8172222 : Nat := 4983230072969 + 3 ^ 40 * 8172222 * 2
def baseEnd_8172222 : Nat := 4196277901247430377541641

theorem tailTrace_8172222 : CollatzResearch.WordTrace tailWord_8172222 prefixEnd_8172222 4196277901247430377541641 := by
  unfold tailWord_8172222
  simp only [CollatzResearch.WordTrace]
  refine ⟨37258177924930359155625865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198710282266295248830004613 37258177924930359155625865)
  ·
    refine ⟨27943633443697769366719399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37258177924930359155625865 27943633443697769366719399)
    ·
      refine ⟨41915450165546654050079099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27943633443697769366719399 41915450165546654050079099)
      ·
        refine ⟨62873175248319981075118649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41915450165546654050079099 62873175248319981075118649)
        ·
          refine ⟨47154881436239985806338987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62873175248319981075118649 47154881436239985806338987)
          ·
            refine ⟨70732322154359978709508481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47154881436239985806338987 70732322154359978709508481)
            ·
              refine ⟨53049241615769984032131361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70732322154359978709508481 53049241615769984032131361)
              ·
                refine ⟨39786931211827488024098521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53049241615769984032131361 39786931211827488024098521)
                ·
                  refine ⟨29840198408870616018073891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39786931211827488024098521 29840198408870616018073891)
                  ·
                    refine ⟨44760297613305924027110837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29840198408870616018073891 44760297613305924027110837)
                    ·
                      refine ⟨4196277901247430377541641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44760297613305924027110837 4196277901247430377541641)
                      ·
                        rfl

theorem cell23_8172222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_8172222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172222 prefixEnd_8172222 := by exact prefixLift 8172222
  have htrace : WordTrace (prefixWord ++ tailWord_8172222) baseStart_8172222 baseEnd_8172222 := by
    simpa [prefixWord, tailWord_8172222, baseEnd_8172222] using wordTrace_append hprefix tailTrace_8172222
  have hstable : (prefixWord ++ tailWord_8172222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172222).length < 2 ^ (prefixWord ++ tailWord_8172222).sum := by decide
  have hdescent : baseEnd_8172222 < baseStart_8172222 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172236 : List Nat := [2, 2, 1, 5, 1, 1, 1, 2, 4, 2, 2]
def baseStart_8172236 : Nat := 118140960795 + 8172236 * 2 ^ 59
def prefixEnd_8172236 : Nat := 4983230072969 + 3 ^ 40 * 8172236 * 2
def baseEnd_8172236 : Nat := 4196285089976593322766577

theorem tailTrace_8172236 : CollatzResearch.WordTrace tailWord_8172236 prefixEnd_8172236 4196285089976593322766577 := by
  unfold tailWord_8172236
  simp only [CollatzResearch.WordTrace]
  refine ⟨149032967010696076818008281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198710622680928102424011041 149032967010696076818008281)
  ·
    refine ⟨111774725258022057613506211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149032967010696076818008281 111774725258022057613506211)
    ·
      refine ⟨167662087887033086420259317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111774725258022057613506211 167662087887033086420259317)
      ·
        refine ⟨15718320739409351851899311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167662087887033086420259317 15718320739409351851899311)
        ·
          refine ⟨23577481109114027777848967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15718320739409351851899311 23577481109114027777848967)
          ·
            refine ⟨35366221663671041666773451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23577481109114027777848967 35366221663671041666773451)
            ·
              refine ⟨53049332495506562500160177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35366221663671041666773451 53049332495506562500160177)
              ·
                refine ⟨39786999371629921875120133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53049332495506562500160177 39786999371629921875120133)
                ·
                  refine ⟨7460062382180610351585025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39786999371629921875120133 7460062382180610351585025)
                  ·
                    refine ⟨5595046786635457763688769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7460062382180610351585025 5595046786635457763688769)
                    ·
                      refine ⟨4196285089976593322766577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5595046786635457763688769 4196285089976593322766577)
                      ·
                        rfl

theorem cell23_8172236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_8172236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172236 prefixEnd_8172236 := by exact prefixLift 8172236
  have htrace : WordTrace (prefixWord ++ tailWord_8172236) baseStart_8172236 baseEnd_8172236 := by
    simpa [prefixWord, tailWord_8172236, baseEnd_8172236] using wordTrace_append hprefix tailTrace_8172236
  have hstable : (prefixWord ++ tailWord_8172236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172236).length < 2 ^ (prefixWord ++ tailWord_8172236).sum := by decide
  have hdescent : baseEnd_8172236 < baseStart_8172236 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172259 : List Nat := [1, 1, 1, 7, 1, 3, 1, 1, 7]
def baseStart_8172259 : Nat := 118140960795 + 8172259 * 2 ^ 59
def prefixEnd_8172259 : Nat := 4983230072969 + 3 ^ 40 * 8172259 * 2
def baseEnd_8172259 : Nat := 466255211114627414753219

theorem tailTrace_8172259 : CollatzResearch.WordTrace tailWord_8172259 prefixEnd_8172259 466255211114627414753219 := by
  unfold tailWord_8172259
  simp only [CollatzResearch.WordTrace]
  refine ⟨298066772900308828564103831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198711181933539219042735887 298066772900308828564103831)
  ·
    refine ⟨447100159350463242846155747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298066772900308828564103831 447100159350463242846155747)
    ·
      refine ⟨670650239025694864269233621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447100159350463242846155747 670650239025694864269233621)
      ·
        refine ⟨15718364977164723381310163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 670650239025694864269233621 15718364977164723381310163)
        ·
          refine ⟨23577547465747085071965245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15718364977164723381310163 23577547465747085071965245)
          ·
            refine ⟨8841580299655156901986967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23577547465747085071965245 8841580299655156901986967)
            ·
              refine ⟨13262370449482735352980451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8841580299655156901986967 13262370449482735352980451)
              ·
                refine ⟨19893555674224103029470677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13262370449482735352980451 19893555674224103029470677)
                ·
                  refine ⟨466255211114627414753219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19893555674224103029470677 466255211114627414753219)
                  ·
                    rfl

theorem cell23_8172259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 7].length) (baseStart_8172259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172259 prefixEnd_8172259 := by exact prefixLift 8172259
  have htrace : WordTrace (prefixWord ++ tailWord_8172259) baseStart_8172259 baseEnd_8172259 := by
    simpa [prefixWord, tailWord_8172259, baseEnd_8172259] using wordTrace_append hprefix tailTrace_8172259
  have hstable : (prefixWord ++ tailWord_8172259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172259).length < 2 ^ (prefixWord ++ tailWord_8172259).sum := by decide
  have hdescent : baseEnd_8172259 < baseStart_8172259 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172265 : List Nat := [1, 2, 1, 1, 1, 2, 5, 1, 1, 1, 7]
def baseStart_8172265 : Nat := 118140960795 + 8172265 * 2 ^ 59
def prefixEnd_8172265 : Nat := 4983230072969 + 3 ^ 40 * 8172265 * 2
def baseEnd_8172265 : Nat := 4196299980915573709303943

theorem tailTrace_8172265 : CollatzResearch.WordTrace tailWord_8172265 prefixEnd_8172265 4196299980915573709303943 := by
  unfold tailWord_8172265
  simp only [CollatzResearch.WordTrace]
  refine ⟨298066991738287091588822249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198711327825524727725881499 298066991738287091588822249)
  ·
    refine ⟨223550243803715318691616687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298066991738287091588822249 223550243803715318691616687)
    ·
      refine ⟨335325365705572978037425031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223550243803715318691616687 335325365705572978037425031)
      ·
        refine ⟨502988048558359467056137547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335325365705572978037425031 502988048558359467056137547)
        ·
          refine ⟨754482072837539200584206321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502988048558359467056137547 754482072837539200584206321)
          ·
            refine ⟨565861554628154400438154741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 754482072837539200584206321 565861554628154400438154741)
            ·
              refine ⟨53049520746389475041077007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 565861554628154400438154741 53049520746389475041077007)
              ·
                refine ⟨79574281119584212561615511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53049520746389475041077007 79574281119584212561615511)
                ·
                  refine ⟨119361421679376318842423267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79574281119584212561615511 119361421679376318842423267)
                  ·
                    refine ⟨179042132519064478263634901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 119361421679376318842423267 179042132519064478263634901)
                    ·
                      refine ⟨4196299980915573709303943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 179042132519064478263634901 4196299980915573709303943)
                      ·
                        rfl

theorem cell23_8172265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 1, 7].length) (baseStart_8172265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172265 prefixEnd_8172265 := by exact prefixLift 8172265
  have htrace : WordTrace (prefixWord ++ tailWord_8172265) baseStart_8172265 baseEnd_8172265 := by
    simpa [prefixWord, tailWord_8172265, baseEnd_8172265] using wordTrace_append hprefix tailTrace_8172265
  have hstable : (prefixWord ++ tailWord_8172265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172265).length < 2 ^ (prefixWord ++ tailWord_8172265).sum := by decide
  have hdescent : baseEnd_8172265 < baseStart_8172265 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172270 : List Nat := [4, 1, 2, 1, 1, 5, 2, 1, 2, 2, 2]
def baseStart_8172270 : Nat := 118140960795 + 8172270 * 2 ^ 59
def prefixEnd_8172270 : Nat := 4983230072969 + 3 ^ 40 * 8172270 * 2
def baseEnd_8172270 : Nat := 4196302548318846189741421

theorem tailTrace_8172270 : CollatzResearch.WordTrace tailWord_8172270 prefixEnd_8172270 4196302548318846189741421 := by
  unfold tailWord_8172270
  simp only [CollatzResearch.WordTrace]
  refine ⟨37258396762908622180344283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198711449402179318295169509 37258396762908622180344283)
  ·
    refine ⟨55887595144362933270516425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37258396762908622180344283 55887595144362933270516425)
    ·
      refine ⟨41915696358272199952887319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55887595144362933270516425 41915696358272199952887319)
      ·
        refine ⟨62873544537408299929330979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41915696358272199952887319 62873544537408299929330979)
        ·
          refine ⟨94310316806112449893996469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62873544537408299929330979 94310316806112449893996469)
          ·
            refine ⟨8841592200573042177562169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94310316806112449893996469 8841592200573042177562169)
            ·
              refine ⟨6631194150429781633171627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8841592200573042177562169 6631194150429781633171627)
              ·
                refine ⟨9946791225644672449757441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6631194150429781633171627 9946791225644672449757441)
                ·
                  refine ⟨7460093419233504337318081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9946791225644672449757441 7460093419233504337318081)
                  ·
                    refine ⟨5595070064425128252988561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7460093419233504337318081 5595070064425128252988561)
                    ·
                      refine ⟨4196302548318846189741421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5595070064425128252988561 4196302548318846189741421)
                      ·
                        rfl

theorem cell23_8172270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 1, 2, 2, 2].length) (baseStart_8172270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172270 prefixEnd_8172270 := by exact prefixLift 8172270
  have htrace : WordTrace (prefixWord ++ tailWord_8172270) baseStart_8172270 baseEnd_8172270 := by
    simpa [prefixWord, tailWord_8172270, baseEnd_8172270] using wordTrace_append hprefix tailTrace_8172270
  have hstable : (prefixWord ++ tailWord_8172270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172270).length < 2 ^ (prefixWord ++ tailWord_8172270).sum := by decide
  have hdescent : baseEnd_8172270 < baseStart_8172270 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172309 : List Nat := [1, 3, 2, 1, 2, 2, 2, 2, 2, 4, 2]
def baseStart_8172309 : Nat := 118140960795 + 8172309 * 2 ^ 59
def prefixEnd_8172309 : Nat := 4983230072969 + 3 ^ 40 * 8172309 * 2
def baseEnd_8172309 : Nat := 4196322574064371537153741

theorem tailTrace_8172309 : CollatzResearch.WordTrace tailWord_8172309 prefixEnd_8172309 4196322574064371537153741 := by
  unfold tailWord_8172309
  simp only [CollatzResearch.WordTrace]
  refine ⟨298068596550127687103423981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198712397700085124735615987 298068596550127687103423981)
  ·
    refine ⟨111775723706297882663783993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298068596550127687103423981 111775723706297882663783993)
    ·
      refine ⟨83831792779723411997837995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111775723706297882663783993 83831792779723411997837995)
      ·
        refine ⟨125747689169585117996756993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83831792779723411997837995 125747689169585117996756993)
        ·
          refine ⟨94310766877188838497567745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125747689169585117996756993 94310766877188838497567745)
          ·
            refine ⟨70733075157891628873175809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94310766877188838497567745 70733075157891628873175809)
            ·
              refine ⟨53049806368418721654881857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70733075157891628873175809 53049806368418721654881857)
              ·
                refine ⟨39787354776314041241161393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53049806368418721654881857 39787354776314041241161393)
                ·
                  refine ⟨29840516082235530930871045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39787354776314041241161393 29840516082235530930871045)
                  ·
                    refine ⟨5595096765419162049538321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29840516082235530930871045 5595096765419162049538321)
                    ·
                      refine ⟨4196322574064371537153741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5595096765419162049538321 4196322574064371537153741)
                      ·
                        rfl

theorem cell23_8172309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 4, 2].length) (baseStart_8172309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172309 prefixEnd_8172309 := by exact prefixLift 8172309
  have htrace : WordTrace (prefixWord ++ tailWord_8172309) baseStart_8172309 baseEnd_8172309 := by
    simpa [prefixWord, tailWord_8172309, baseEnd_8172309] using wordTrace_append hprefix tailTrace_8172309
  have hstable : (prefixWord ++ tailWord_8172309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172309).length < 2 ^ (prefixWord ++ tailWord_8172309).sum := by decide
  have hdescent : baseEnd_8172309 < baseStart_8172309 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172312 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 3, 4, 3]
def baseStart_8172312 : Nat := 118140960795 + 8172312 * 2 ^ 59
def prefixEnd_8172312 : Nat := 4983230072969 + 3 ^ 40 * 8172312 * 2
def baseEnd_8172312 : Nat := 4196324114506335025416227

theorem tailTrace_8172312 : CollatzResearch.WordTrace tailWord_8172312 prefixEnd_8172312 4196324114506335025416227 := by
  unfold tailWord_8172312
  simp only [CollatzResearch.WordTrace]
  refine ⟨149034352984558409307891595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198712470646077879077188793 149034352984558409307891595)
  ·
    refine ⟨223551529476837613961837393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149034352984558409307891595 223551529476837613961837393)
    ·
      refine ⟨167663647107628210471378045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223551529476837613961837393 167663647107628210471378045)
      ·
        refine ⟨62873867665360578926766767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167663647107628210471378045 62873867665360578926766767)
        ·
          refine ⟨94310801498040868390150151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62873867665360578926766767 94310801498040868390150151)
          ·
            refine ⟨141466202247061302585225227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94310801498040868390150151 141466202247061302585225227)
            ·
              refine ⟨212199303370591953877837841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141466202247061302585225227 212199303370591953877837841)
              ·
                refine ⟨159149477527943965408378381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212199303370591953877837841 159149477527943965408378381)
                ·
                  refine ⟨59681054072978987028141893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159149477527943965408378381 59681054072978987028141893)
                  ·
                    refine ⟨11190197638683560067776605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59681054072978987028141893 11190197638683560067776605)
                    ·
                      refine ⟨4196324114506335025416227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11190197638683560067776605 4196324114506335025416227)
                      ·
                        rfl

theorem cell23_8172312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_8172312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172312 prefixEnd_8172312 := by exact prefixLift 8172312
  have htrace : WordTrace (prefixWord ++ tailWord_8172312) baseStart_8172312 baseEnd_8172312 := by
    simpa [prefixWord, tailWord_8172312, baseEnd_8172312] using wordTrace_append hprefix tailTrace_8172312
  have hstable : (prefixWord ++ tailWord_8172312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172312).length < 2 ^ (prefixWord ++ tailWord_8172312).sum := by decide
  have hdescent : baseEnd_8172312 < baseStart_8172312 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172332 : List Nat := [2, 2, 1, 1, 1, 4, 1, 5, 6]
def baseStart_8172332 : Nat := 118140960795 + 8172332 * 2 ^ 59
def prefixEnd_8172332 : Nat := 4983230072969 + 3 ^ 40 * 8172332 * 2
def baseEnd_8172332 : Nat := 466259376013269438574015

theorem tailTrace_8172332 : CollatzResearch.WordTrace tailWord_8172332 prefixEnd_8172332 466259376013269438574015 := by
  unfold tailWord_8172332
  simp only [CollatzResearch.WordTrace]
  refine ⟨149034717714522181015755625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198712956952696241354340833 149034717714522181015755625)
  ·
    refine ⟨111776038285891635761816719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149034717714522181015755625 111776038285891635761816719)
    ·
      refine ⟨167664057428837453642725079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111776038285891635761816719 167664057428837453642725079)
      ·
        refine ⟨251496086143256180464087619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167664057428837453642725079 251496086143256180464087619)
        ·
          refine ⟨377244129214884270696131429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251496086143256180464087619 377244129214884270696131429)
          ·
            refine ⟨70733274227790800755524643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 377244129214884270696131429 70733274227790800755524643)
            ·
              refine ⟨106099911341686201133286965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70733274227790800755524643 106099911341686201133286965)
              ·
                refine ⟨9946866688283081356245653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106099911341686201133286965 9946866688283081356245653)
                ·
                  refine ⟨466259376013269438574015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9946866688283081356245653 466259376013269438574015)
                  ·
                    rfl

theorem cell23_8172332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 6].length) (baseStart_8172332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172332 prefixEnd_8172332 := by exact prefixLift 8172332
  have htrace : WordTrace (prefixWord ++ tailWord_8172332) baseStart_8172332 baseEnd_8172332 := by
    simpa [prefixWord, tailWord_8172332, baseEnd_8172332] using wordTrace_append hprefix tailTrace_8172332
  have hstable : (prefixWord ++ tailWord_8172332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172332).length < 2 ^ (prefixWord ++ tailWord_8172332).sum := by decide
  have hdescent : baseEnd_8172332 < baseStart_8172332 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172359 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 7, 1, 3]
def baseStart_8172359 : Nat := 118140960795 + 8172359 * 2 ^ 59
def prefixEnd_8172359 : Nat := 4983230072969 + 3 ^ 40 * 8172359 * 2
def baseEnd_8172359 : Nat := 4196348248097096341528511

theorem tailTrace_8172359 : CollatzResearch.WordTrace tailWord_8172359 prefixEnd_8172359 4196348248097096341528511 := by
  unfold tailWord_8172359
  simp only [CollatzResearch.WordTrace]
  refine ⟨298070420199946545642744131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198713613466631030428496087 298070420199946545642744131)
  ·
    refine ⟨447105630299919818464116197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298070420199946545642744131 447105630299919818464116197)
    ·
      refine ⟨83832305681234965962021787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 447105630299919818464116197 83832305681234965962021787)
      ·
        refine ⟨125748458521852448943032681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83832305681234965962021787 125748458521852448943032681)
        ·
          refine ⟨94311343891389336707274511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125748458521852448943032681 94311343891389336707274511)
          ·
            refine ⟨141467015837084005060911767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94311343891389336707274511 141467015837084005060911767)
            ·
              refine ⟨212200523755626007591367651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141467015837084005060911767 212200523755626007591367651)
              ·
                refine ⟨318300785633439011387051477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212200523755626007591367651 318300785633439011387051477)
                ·
                  refine ⟨7460174663283726829384019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 318300785633439011387051477 7460174663283726829384019)
                  ·
                    refine ⟨11190261994925590244076029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7460174663283726829384019 11190261994925590244076029)
                    ·
                      refine ⟨4196348248097096341528511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11190261994925590244076029 4196348248097096341528511)
                      ·
                        rfl

theorem cell23_8172359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 7, 1, 3].length) (baseStart_8172359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172359 prefixEnd_8172359 := by exact prefixLift 8172359
  have htrace : WordTrace (prefixWord ++ tailWord_8172359) baseStart_8172359 baseEnd_8172359 := by
    simpa [prefixWord, tailWord_8172359, baseEnd_8172359] using wordTrace_append hprefix tailTrace_8172359
  have hstable : (prefixWord ++ tailWord_8172359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172359).length < 2 ^ (prefixWord ++ tailWord_8172359).sum := by decide
  have hdescent : baseEnd_8172359 < baseStart_8172359 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172362 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 5, 5]
def baseStart_8172362 : Nat := 118140960795 + 8172362 * 2 ^ 59
def prefixEnd_8172362 : Nat := 4983230072969 + 3 ^ 40 * 8172362 * 2
def baseEnd_8172362 : Nat := 1398783262846353276596999

theorem tailTrace_8172362 : CollatzResearch.WordTrace tailWord_8172362 prefixEnd_8172362 1398783262846353276596999 := by
  unfold tailWord_8172362
  simp only [CollatzResearch.WordTrace]
  refine ⟨74517632404733919288775835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198713686412623784770068893 74517632404733919288775835)
  ·
    refine ⟨111776448607100878933163753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74517632404733919288775835 111776448607100878933163753)
    ·
      refine ⟨83832336455325659199872815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111776448607100878933163753 83832336455325659199872815)
      ·
        refine ⟨125748504682988488799809223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83832336455325659199872815 125748504682988488799809223)
        ·
          refine ⟨188622757024482733199713835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125748504682988488799809223 188622757024482733199713835)
          ·
            refine ⟨282934135536724099799570753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188622757024482733199713835 282934135536724099799570753)
            ·
              refine ⟨212200601652543074849678065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282934135536724099799570753 212200601652543074849678065)
              ·
                refine ⟨159150451239407306137258549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212200601652543074849678065 159150451239407306137258549)
                ·
                  refine ⟨14920354803694434950367989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 159150451239407306137258549 14920354803694434950367989)
                  ·
                    refine ⟨1398783262846353276596999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14920354803694434950367989 1398783262846353276596999)
                    ·
                      rfl

theorem cell23_8172362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_8172362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172362 prefixEnd_8172362 := by exact prefixLift 8172362
  have htrace : WordTrace (prefixWord ++ tailWord_8172362) baseStart_8172362 baseEnd_8172362 := by
    simpa [prefixWord, tailWord_8172362, baseEnd_8172362] using wordTrace_append hprefix tailTrace_8172362
  have hstable : (prefixWord ++ tailWord_8172362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172362).length < 2 ^ (prefixWord ++ tailWord_8172362).sum := by decide
  have hdescent : baseEnd_8172362 < baseStart_8172362 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172409 : List Nat := [1, 2, 1, 3, 2, 3, 1, 2, 4, 4]
def baseStart_8172409 : Nat := 118140960795 + 8172409 * 2 ^ 59
def prefixEnd_8172409 : Nat := 4983230072969 + 3 ^ 40 * 8172409 * 2
def baseEnd_8172409 : Nat := 1398791307376607048634427

theorem tailTrace_8172409 : CollatzResearch.WordTrace tailWord_8172409 prefixEnd_8172409 1398791307376607048634427 := by
  unfold tailWord_8172409
  simp only [CollatzResearch.WordTrace]
  refine ⟨298072243849765404182064281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198714829233176936121376187 298072243849765404182064281)
  ·
    refine ⟨223554182887324053136548211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298072243849765404182064281 223554182887324053136548211)
    ·
      refine ⟨335331274330986079704822317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223554182887324053136548211 335331274330986079704822317)
      ·
        refine ⟨125749227874119779889308369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335331274330986079704822317 125749227874119779889308369)
        ·
          refine ⟨94311920905589834916981277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125749227874119779889308369 94311920905589834916981277)
          ·
            refine ⟨35366970339596188093867979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94311920905589834916981277 35366970339596188093867979)
            ·
              refine ⟨53050455509394282140801969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35366970339596188093867979 53050455509394282140801969)
              ·
                refine ⟨39787841632045711605601477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53050455509394282140801969 39787841632045711605601477)
                ·
                  refine ⟨7460220306008570926050277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39787841632045711605601477 7460220306008570926050277)
                  ·
                    refine ⟨1398791307376607048634427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7460220306008570926050277 1398791307376607048634427)
                    ·
                      rfl

theorem cell23_8172409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 4, 4].length) (baseStart_8172409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172409 prefixEnd_8172409 := by exact prefixLift 8172409
  have htrace : WordTrace (prefixWord ++ tailWord_8172409) baseStart_8172409 baseEnd_8172409 := by
    simpa [prefixWord, tailWord_8172409, baseEnd_8172409] using wordTrace_append hprefix tailTrace_8172409
  have hstable : (prefixWord ++ tailWord_8172409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172409).length < 2 ^ (prefixWord ++ tailWord_8172409).sum := by decide
  have hdescent : baseEnd_8172409 < baseStart_8172409 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172419 : List Nat := [1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 5]
def baseStart_8172419 : Nat := 118140960795 + 8172419 * 2 ^ 59
def prefixEnd_8172419 : Nat := 4983230072969 + 3 ^ 40 * 8172419 * 2
def baseEnd_8172419 : Nat := 4196379056936366106778235

theorem tailTrace_8172419 : CollatzResearch.WordTrace tailWord_8172419 prefixEnd_8172419 4196379056936366106778235 := by
  unfold tailWord_8172419
  simp only [CollatzResearch.WordTrace]
  refine ⟨298072608579729175889928311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198715072386486117259952207 298072608579729175889928311)
  ·
    refine ⟨447108912869593763834892467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298072608579729175889928311 447108912869593763834892467)
    ·
      refine ⟨670663369304390645752338701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447108912869593763834892467 670663369304390645752338701)
      ·
        refine ⟨251498763489146492157127013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 670663369304390645752338701 251498763489146492157127013)
        ·
          refine ⟨47156018154214967279461315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 251498763489146492157127013 47156018154214967279461315)
          ·
            refine ⟨70734027231322450919191973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47156018154214967279461315 70734027231322450919191973)
            ·
              refine ⟨13262630105872959547348495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70734027231322450919191973 13262630105872959547348495)
              ·
                refine ⟨19893945158809439321022743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13262630105872959547348495 19893945158809439321022743)
                ·
                  refine ⟨29840917738214158981534115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19893945158809439321022743 29840917738214158981534115)
                  ·
                    refine ⟨44761376607321238472301173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29840917738214158981534115 44761376607321238472301173)
                    ·
                      refine ⟨4196379056936366106778235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44761376607321238472301173 4196379056936366106778235)
                      ·
                        rfl

theorem cell23_8172419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 5].length) (baseStart_8172419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172419 prefixEnd_8172419 := by exact prefixLift 8172419
  have htrace : WordTrace (prefixWord ++ tailWord_8172419) baseStart_8172419 baseEnd_8172419 := by
    simpa [prefixWord, tailWord_8172419, baseEnd_8172419] using wordTrace_append hprefix tailTrace_8172419
  have hstable : (prefixWord ++ tailWord_8172419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172419).length < 2 ^ (prefixWord ++ tailWord_8172419).sum := by decide
  have hdescent : baseEnd_8172419 < baseStart_8172419 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172426 : List Nat := [3, 1, 2, 4, 1, 1, 2, 1, 4, 4]
def baseStart_8172426 : Nat := 118140960795 + 8172426 * 2 ^ 59
def prefixEnd_8172426 : Nat := 4983230072969 + 3 ^ 40 * 8172426 * 2
def baseEnd_8172426 : Nat := 1398794217100315859796901

theorem tailTrace_8172426 : CollatzResearch.WordTrace tailWord_8172426 prefixEnd_8172426 1398794217100315859796901 := by
  unfold tailWord_8172426
  simp only [CollatzResearch.WordTrace]
  refine ⟨74518215972675954021358283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198715242593802544056955421 74518215972675954021358283)
  ·
    refine ⟨111777323959013931032037425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74518215972675954021358283 111777323959013931032037425)
    ·
      refine ⟨83832992969260448274028069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111777323959013931032037425 83832992969260448274028069)
      ·
        refine ⟨15718686181736334051380263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83832992969260448274028069 15718686181736334051380263)
        ·
          refine ⟨23578029272604501077070395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15718686181736334051380263 23578029272604501077070395)
          ·
            refine ⟨35367043908906751615605593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23578029272604501077070395 35367043908906751615605593)
            ·
              refine ⟨26525282931680063711704195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35367043908906751615605593 26525282931680063711704195)
              ·
                refine ⟨39787924397520095567556293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26525282931680063711704195 39787924397520095567556293)
                ·
                  refine ⟨7460235824535017918916805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39787924397520095567556293 7460235824535017918916805)
                  ·
                    refine ⟨1398794217100315859796901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7460235824535017918916805 1398794217100315859796901)
                    ·
                      rfl

theorem cell23_8172426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 4, 4].length) (baseStart_8172426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172426 prefixEnd_8172426 := by exact prefixLift 8172426
  have htrace : WordTrace (prefixWord ++ tailWord_8172426) baseStart_8172426 baseEnd_8172426 := by
    simpa [prefixWord, tailWord_8172426, baseEnd_8172426] using wordTrace_append hprefix tailTrace_8172426
  have hstable : (prefixWord ++ tailWord_8172426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172426).length < 2 ^ (prefixWord ++ tailWord_8172426).sum := by decide
  have hdescent : baseEnd_8172426 < baseStart_8172426 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172436 : List Nat := [2, 4, 2, 1, 1, 1, 2, 2, 3, 2, 3]
def baseStart_8172436 : Nat := 118140960795 + 8172436 * 2 ^ 59
def prefixEnd_8172436 : Nat := 4983230072969 + 3 ^ 40 * 8172436 * 2
def baseEnd_8172436 : Nat := 4196387786107492540265657

theorem tailTrace_8172436 : CollatzResearch.WordTrace tailWord_8172436 prefixEnd_8172436 4196387786107492540265657 := by
  unfold tailWord_8172436
  simp only [CollatzResearch.WordTrace]
  refine ⟨149036614310333793896648581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198715485747111725195531441 149036614310333793896648581)
  ·
    refine ⟨27944365183187586355621609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149036614310333793896648581 27944365183187586355621609)
    ·
      refine ⟨20958273887390689766716207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27944365183187586355621609 20958273887390689766716207)
      ·
        refine ⟨31437410831086034650074311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20958273887390689766716207 31437410831086034650074311)
        ·
          refine ⟨47156116246629051975111467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31437410831086034650074311 47156116246629051975111467)
          ·
            refine ⟨70734174369943577962667201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47156116246629051975111467 70734174369943577962667201)
            ·
              refine ⟨53050630777457683472000401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70734174369943577962667201 53050630777457683472000401)
              ·
                refine ⟨39787973083093262604000301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53050630777457683472000401 39787973083093262604000301)
                ·
                  refine ⟨14920489906159973476500113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39787973083093262604000301 14920489906159973476500113)
                  ·
                    refine ⟨11190367429619980107375085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14920489906159973476500113 11190367429619980107375085)
                    ·
                      refine ⟨4196387786107492540265657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11190367429619980107375085 4196387786107492540265657)
                      ·
                        rfl

theorem cell23_8172436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_8172436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172436 prefixEnd_8172436 := by exact prefixLift 8172436
  have htrace : WordTrace (prefixWord ++ tailWord_8172436) baseStart_8172436 baseEnd_8172436 := by
    simpa [prefixWord, tailWord_8172436, baseEnd_8172436] using wordTrace_append hprefix tailTrace_8172436
  have hstable : (prefixWord ++ tailWord_8172436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172436).length < 2 ^ (prefixWord ++ tailWord_8172436).sum := by decide
  have hdescent : baseEnd_8172436 < baseStart_8172436 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172459 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 2, 7, 2]
def baseStart_8172459 : Nat := 118140960795 + 8172459 * 2 ^ 59
def prefixEnd_8172459 : Nat := 4983230072969 + 3 ^ 40 * 8172459 * 2
def baseEnd_8172459 : Nat := 4196399596162545950278051

theorem tailTrace_8172459 : CollatzResearch.WordTrace tailWord_8172459 prefixEnd_8172459 4196399596162545950278051 := by
  unfold tailWord_8172459
  simp only [CollatzResearch.WordTrace]
  refine ⟨298074067499584262721384431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198716044999722841814256287 298074067499584262721384431)
  ·
    refine ⟨447111101249376394082076647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298074067499584262721384431 447111101249376394082076647)
    ·
      refine ⟨670666651874064591123114971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447111101249376394082076647 670666651874064591123114971)
      ·
        refine ⟨1005999977811096886684672457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 670666651874064591123114971 1005999977811096886684672457)
        ·
          refine ⟨754499983358322665013504343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1005999977811096886684672457 754499983358322665013504343)
          ·
            refine ⟨1131749975037483997520256515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754499983358322665013504343 1131749975037483997520256515)
            ·
              refine ⟨1697624962556225996280384773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1131749975037483997520256515 1697624962556225996280384773)
              ·
                refine ⟨318304680479292374302572145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1697624962556225996280384773 318304680479292374302572145)
                ·
                  refine ⟨238728510359469280726929109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 318304680479292374302572145 238728510359469280726929109)
                  ·
                    refine ⟨5595199461550061267037401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 238728510359469280726929109 5595199461550061267037401)
                    ·
                      refine ⟨4196399596162545950278051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5595199461550061267037401 4196399596162545950278051)
                      ·
                        rfl

theorem cell23_8172459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 7, 2].length) (baseStart_8172459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172459 prefixEnd_8172459 := by exact prefixLift 8172459
  have htrace : WordTrace (prefixWord ++ tailWord_8172459) baseStart_8172459 baseEnd_8172459 := by
    simpa [prefixWord, tailWord_8172459, baseEnd_8172459] using wordTrace_append hprefix tailTrace_8172459
  have hstable : (prefixWord ++ tailWord_8172459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172459).length < 2 ^ (prefixWord ++ tailWord_8172459).sum := by decide
  have hdescent : baseEnd_8172459 < baseStart_8172459 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172484 : List Nat := [2, 3, 3, 3, 1, 1, 1, 4, 1, 2, 2]
def baseStart_8172484 : Nat := 118140960795 + 8172484 * 2 ^ 59
def prefixEnd_8172484 : Nat := 4983230072969 + 3 ^ 40 * 8172484 * 2
def baseEnd_8172484 : Nat := 4196412433178908352465437

theorem tailTrace_8172484 : CollatzResearch.WordTrace tailWord_8172484 prefixEnd_8172484 4196412433178908352465437 := by
  unfold tailWord_8172484
  simp only [CollatzResearch.WordTrace]
  refine ⟨149037489662246845995522253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198716652882995794660696337 149037489662246845995522253)
  ·
    refine ⟨55889058623342567248320845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149037489662246845995522253 55889058623342567248320845)
    ·
      refine ⟨20958396983753462718120317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55889058623342567248320845 20958396983753462718120317)
      ·
        refine ⟨7859398868907548519295119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20958396983753462718120317 7859398868907548519295119)
        ·
          refine ⟨11789098303361322778942679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7859398868907548519295119 11789098303361322778942679)
          ·
            refine ⟨17683647455041984168414019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11789098303361322778942679 17683647455041984168414019)
            ·
              refine ⟨26525471182562976252621029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17683647455041984168414019 26525471182562976252621029)
              ·
                refine ⟨4973525846730558047366443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26525471182562976252621029 4973525846730558047366443)
                ·
                  refine ⟨7460288770095837071049665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4973525846730558047366443 7460288770095837071049665)
                  ·
                    refine ⟨5595216577571877803287249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7460288770095837071049665 5595216577571877803287249)
                    ·
                      refine ⟨4196412433178908352465437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5595216577571877803287249 4196412433178908352465437)
                      ·
                        rfl

theorem cell23_8172484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_8172484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172484 prefixEnd_8172484 := by exact prefixLift 8172484
  have htrace : WordTrace (prefixWord ++ tailWord_8172484) baseStart_8172484 baseEnd_8172484 := by
    simpa [prefixWord, tailWord_8172484, baseEnd_8172484] using wordTrace_append hprefix tailTrace_8172484
  have hstable : (prefixWord ++ tailWord_8172484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172484).length < 2 ^ (prefixWord ++ tailWord_8172484).sum := by decide
  have hdescent : baseEnd_8172484 < baseStart_8172484 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172540 : List Nat := [2, 2, 2, 1, 2, 3, 3, 2, 2, 2, 2]
def baseStart_8172540 : Nat := 118140960795 + 8172540 * 2 ^ 59
def prefixEnd_8172540 : Nat := 4983230072969 + 3 ^ 40 * 8172540 * 2
def baseEnd_8172540 : Nat := 4196441188095560133365179

theorem tailTrace_8172540 : CollatzResearch.WordTrace tailWord_8172540 prefixEnd_8172540 4196441188095560133365179 := by
  unfold tailWord_8172540
  simp only [CollatzResearch.WordTrace]
  refine ⟨149038510906145406777541537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198718014541527209036722049 149038510906145406777541537)
  ·
    refine ⟨111778883179609055083156153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149038510906145406777541537 111778883179609055083156153)
    ·
      refine ⟨83834162384706791312367115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111778883179609055083156153 83834162384706791312367115)
      ·
        refine ⟨125751243577060186968550673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83834162384706791312367115 125751243577060186968550673)
        ·
          refine ⟨94313432682795140226413005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125751243577060186968550673 94313432682795140226413005)
          ·
            refine ⟨35367537256048177584904877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94313432682795140226413005 35367537256048177584904877)
            ·
              refine ⟨13262826471018066594339329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35367537256048177584904877 13262826471018066594339329)
              ·
                refine ⟨9947119853263549945754497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13262826471018066594339329 9947119853263549945754497)
                ·
                  refine ⟨7460339889947662459315873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9947119853263549945754497 7460339889947662459315873)
                  ·
                    refine ⟨5595254917460746844486905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7460339889947662459315873 5595254917460746844486905)
                    ·
                      refine ⟨4196441188095560133365179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5595254917460746844486905 4196441188095560133365179)
                      ·
                        rfl

theorem cell23_8172540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2, 2, 2, 2].length) (baseStart_8172540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172540 prefixEnd_8172540 := by exact prefixLift 8172540
  have htrace : WordTrace (prefixWord ++ tailWord_8172540) baseStart_8172540 baseEnd_8172540 := by
    simpa [prefixWord, tailWord_8172540, baseEnd_8172540] using wordTrace_append hprefix tailTrace_8172540
  have hstable : (prefixWord ++ tailWord_8172540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172540).length < 2 ^ (prefixWord ++ tailWord_8172540).sum := by decide
  have hdescent : baseEnd_8172540 < baseStart_8172540 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172556 : List Nat := [2, 2, 1, 2, 3, 2, 2, 1, 2, 3, 3]
def baseStart_8172556 : Nat := 118140960795 + 8172556 * 2 ^ 59
def prefixEnd_8172556 : Nat := 4983230072969 + 3 ^ 40 * 8172556 * 2
def baseEnd_8172556 : Nat := 4196449403786032070765105

theorem tailTrace_8172556 : CollatzResearch.WordTrace tailWord_8172556 prefixEnd_8172556 4196449403786032070765105 := by
  unfold tailWord_8172556
  simp only [CollatzResearch.WordTrace]
  refine ⟨149038802690116424143832761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198718403586821898858443681 149038802690116424143832761)
  ·
    refine ⟨111779102017587318107874571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149038802690116424143832761 111779102017587318107874571)
    ·
      refine ⟨167668653026380977161811857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111779102017587318107874571 167668653026380977161811857)
      ·
        refine ⟨125751489769785732871358893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167668653026380977161811857 125751489769785732871358893)
        ·
          refine ⟨47156808663669649826759585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125751489769785732871358893 47156808663669649826759585)
          ·
            refine ⟨35367606497752237370069689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47156808663669649826759585 35367606497752237370069689)
            ·
              refine ⟨26525704873314178027552267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35367606497752237370069689 26525704873314178027552267)
              ·
                refine ⟨39788557309971267041328401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26525704873314178027552267 39788557309971267041328401)
                ·
                  refine ⟨29841417982478450280996301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39788557309971267041328401 29841417982478450280996301)
                  ·
                    refine ⟨11190531743429418855373613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29841417982478450280996301 11190531743429418855373613)
                    ·
                      refine ⟨4196449403786032070765105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11190531743429418855373613 4196449403786032070765105)
                      ·
                        rfl

theorem cell23_8172556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 2, 3, 3].length) (baseStart_8172556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172556 prefixEnd_8172556 := by exact prefixLift 8172556
  have htrace : WordTrace (prefixWord ++ tailWord_8172556) baseStart_8172556 baseEnd_8172556 := by
    simpa [prefixWord, tailWord_8172556, baseEnd_8172556] using wordTrace_append hprefix tailTrace_8172556
  have hstable : (prefixWord ++ tailWord_8172556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172556).length < 2 ^ (prefixWord ++ tailWord_8172556).sum := by decide
  have hdescent : baseEnd_8172556 < baseStart_8172556 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172580 : List Nat := [2, 3, 1, 4, 1, 3, 1, 3, 5]
def baseStart_8172580 : Nat := 118140960795 + 8172580 * 2 ^ 59
def prefixEnd_8172580 : Nat := 4983230072969 + 3 ^ 40 * 8172580 * 2
def baseEnd_8172580 : Nat := 466273525257971108540555

theorem tailTrace_8172580 : CollatzResearch.WordTrace tailWord_8172580 prefixEnd_8172580 466273525257971108540555 := by
  unfold tailWord_8172580
  simp only [CollatzResearch.WordTrace]
  refine ⟨149039240366072950193269597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198718987154763933591026129 149039240366072950193269597)
  ·
    refine ⟨55889715137277356322476099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149039240366072950193269597 55889715137277356322476099)
    ·
      refine ⟨83834572705916034483714149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55889715137277356322476099 83834572705916034483714149)
      ·
        refine ⟨15718982382359256465696403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83834572705916034483714149 15718982382359256465696403)
        ·
          refine ⟨23578473573538884698544605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15718982382359256465696403 23578473573538884698544605)
          ·
            refine ⟨8841927590077081761954227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23578473573538884698544605 8841927590077081761954227)
            ·
              refine ⟨13262891385115622642931341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8841927590077081761954227 13262891385115622642931341)
              ·
                refine ⟨4973584269418358491099253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13262891385115622642931341 4973584269418358491099253)
                ·
                  refine ⟨466273525257971108540555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4973584269418358491099253 466273525257971108540555)
                  ·
                    rfl

theorem cell23_8172580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 3, 5].length) (baseStart_8172580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172580 prefixEnd_8172580 := by exact prefixLift 8172580
  have htrace : WordTrace (prefixWord ++ tailWord_8172580) baseStart_8172580 baseEnd_8172580 := by
    simpa [prefixWord, tailWord_8172580, baseEnd_8172580] using wordTrace_append hprefix tailTrace_8172580
  have hstable : (prefixWord ++ tailWord_8172580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172580).length < 2 ^ (prefixWord ++ tailWord_8172580).sum := by decide
  have hdescent : baseEnd_8172580 < baseStart_8172580 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172616 : List Nat := [2, 1, 3, 1, 1, 1, 3, 2, 4, 2, 3]
def baseStart_8172616 : Nat := 118140960795 + 8172616 * 2 ^ 59
def prefixEnd_8172616 : Nat := 4983230072969 + 3 ^ 40 * 8172616 * 2
def baseEnd_8172616 : Nat := 4196480212625301836014829

theorem tailTrace_8172616 : CollatzResearch.WordTrace tailWord_8172616 prefixEnd_8172616 4196480212625301836014829 := by
  unfold tailWord_8172616
  simp only [CollatzResearch.WordTrace]
  refine ⟨149039896880007739267424851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198719862506676985689899801 149039896880007739267424851)
  ·
    refine ⟨223559845320011608901137277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149039896880007739267424851 223559845320011608901137277)
    ·
      refine ⟨83834941995004353337926479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223559845320011608901137277 83834941995004353337926479)
      ·
        refine ⟨125752412992506530006889719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83834941995004353337926479 125752412992506530006889719)
        ·
          refine ⟨188628619488759795010334579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125752412992506530006889719 188628619488759795010334579)
          ·
            refine ⟨282942929233139692515501869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188628619488759795010334579 282942929233139692515501869)
            ·
              refine ⟨106103598462427384693313201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 282942929233139692515501869 106103598462427384693313201)
              ·
                refine ⟨79577698846820538519984901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106103598462427384693313201 79577698846820538519984901)
                ·
                  refine ⟨14920818533778850972497169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79577698846820538519984901 14920818533778850972497169)
                  ·
                    refine ⟨11190613900334138229372877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14920818533778850972497169 11190613900334138229372877)
                    ·
                      refine ⟨4196480212625301836014829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11190613900334138229372877 4196480212625301836014829)
                      ·
                        rfl

theorem cell23_8172616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 4, 2, 3].length) (baseStart_8172616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172616 prefixEnd_8172616 := by exact prefixLift 8172616
  have htrace : WordTrace (prefixWord ++ tailWord_8172616) baseStart_8172616 baseEnd_8172616 := by
    simpa [prefixWord, tailWord_8172616, baseEnd_8172616] using wordTrace_append hprefix tailTrace_8172616
  have hstable : (prefixWord ++ tailWord_8172616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172616).length < 2 ^ (prefixWord ++ tailWord_8172616).sum := by decide
  have hdescent : baseEnd_8172616 < baseStart_8172616 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172653 : List Nat := [1, 5, 1, 1, 2, 3, 2, 2, 6]
def baseStart_8172653 : Nat := 118140960795 + 8172653 * 2 ^ 59
def prefixEnd_8172653 : Nat := 4983230072969 + 3 ^ 40 * 8172653 * 2
def baseEnd_8172653 : Nat := 466277690156613132361351

theorem tailTrace_8172653 : CollatzResearch.WordTrace tailWord_8172653 prefixEnd_8172653 466277690156613132361351 := by
  unfold tailWord_8172653
  simp only [CollatzResearch.WordTrace]
  refine ⟨298081143260881433853946613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198720762173920955902631075 298081143260881433853946613)
  ·
    refine ⟨27945107180707634423807495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 298081143260881433853946613 27945107180707634423807495)
    ·
      refine ⟨41917660771061451635711243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27945107180707634423807495 41917660771061451635711243)
      ·
        refine ⟨62876491156592177453566865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41917660771061451635711243 62876491156592177453566865)
        ·
          refine ⟨47157368367444133090175149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62876491156592177453566865 47157368367444133090175149)
          ·
            refine ⟨17684013137791549908815681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47157368367444133090175149 17684013137791549908815681)
            ·
              refine ⟨13263009853343662431611761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17684013137791549908815681 13263009853343662431611761)
              ·
                refine ⟨9947257390007746823708821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13263009853343662431611761 9947257390007746823708821)
                ·
                  refine ⟨466277690156613132361351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9947257390007746823708821 466277690156613132361351)
                  ·
                    rfl

theorem cell23_8172653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_8172653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172653 prefixEnd_8172653 := by exact prefixLift 8172653
  have htrace : WordTrace (prefixWord ++ tailWord_8172653) baseStart_8172653 baseEnd_8172653 := by
    simpa [prefixWord, tailWord_8172653, baseEnd_8172653] using wordTrace_append hprefix tailTrace_8172653
  have hstable : (prefixWord ++ tailWord_8172653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172653).length < 2 ^ (prefixWord ++ tailWord_8172653).sum := by decide
  have hdescent : baseEnd_8172653 < baseStart_8172653 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172659 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 5]
def baseStart_8172659 : Nat := 118140960795 + 8172659 * 2 ^ 59
def prefixEnd_8172659 : Nat := 4983230072969 + 3 ^ 40 * 8172659 * 2
def baseEnd_8172659 : Nat := 4196502292293445167777131

theorem tailTrace_8172659 : CollatzResearch.WordTrace tailWord_8172659 prefixEnd_8172659 4196502292293445167777131 := by
  unfold tailWord_8172659
  simp only [CollatzResearch.WordTrace]
  refine ⟨298081362098859696878665031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198720908065906464585776687 298081362098859696878665031)
  ·
    refine ⟨447122043148289545317997547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298081362098859696878665031 447122043148289545317997547)
    ·
      refine ⟨670683064722434317976996321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447122043148289545317997547 670683064722434317976996321)
      ·
        refine ⟨503012298541825738482747241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 670683064722434317976996321 503012298541825738482747241)
        ·
          refine ⟨377259223906369303862060431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 503012298541825738482747241 377259223906369303862060431)
          ·
            refine ⟨565888835859553955793090647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377259223906369303862060431 565888835859553955793090647)
            ·
              refine ⟨848833253789330933689635971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 565888835859553955793090647 848833253789330933689635971)
              ·
                refine ⟨1273249880683996400534453957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 848833253789330933689635971 1273249880683996400534453957)
                ·
                  refine ⟨238734352628249325100210117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1273249880683996400534453957 238734352628249325100210117)
                  ·
                    refine ⟨44762691117796748456289397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 238734352628249325100210117 44762691117796748456289397)
                    ·
                      refine ⟨4196502292293445167777131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44762691117796748456289397 4196502292293445167777131)
                      ·
                        rfl

theorem cell23_8172659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 5].length) (baseStart_8172659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172659 prefixEnd_8172659 := by exact prefixLift 8172659
  have htrace : WordTrace (prefixWord ++ tailWord_8172659) baseStart_8172659 baseEnd_8172659 := by
    simpa [prefixWord, tailWord_8172659, baseEnd_8172659] using wordTrace_append hprefix tailTrace_8172659
  have hstable : (prefixWord ++ tailWord_8172659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172659).length < 2 ^ (prefixWord ++ tailWord_8172659).sum := by decide
  have hdescent : baseEnd_8172659 < baseStart_8172659 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172663 : List Nat := [1, 1, 3, 1, 1, 4, 2, 3, 3, 1, 3]
def baseStart_8172663 : Nat := 118140960795 + 8172663 * 2 ^ 59
def prefixEnd_8172663 : Nat := 4983230072969 + 3 ^ 40 * 8172663 * 2
def baseEnd_8172663 : Nat := 4196504346216063152127113

theorem tailTrace_8172663 : CollatzResearch.WordTrace tailWord_8172663 prefixEnd_8172663 4196504346216063152127113 := by
  unfold tailWord_8172663
  simp only [CollatzResearch.WordTrace]
  refine ⟨298081507990845205561810643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198721005327230137041207095 298081507990845205561810643)
  ·
    refine ⟨447122261986267808342715965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298081507990845205561810643 447122261986267808342715965)
    ·
      refine ⟨167670848244850428128518487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 447122261986267808342715965 167670848244850428128518487)
      ·
        refine ⟨251506272367275642192777731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167670848244850428128518487 251506272367275642192777731)
        ·
          refine ⟨377259408550913463289166597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251506272367275642192777731 377259408550913463289166597)
          ·
            refine ⟨70736139103296274366718737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 377259408550913463289166597 70736139103296274366718737)
            ·
              refine ⟨53052104327472205775039053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70736139103296274366718737 53052104327472205775039053)
              ·
                refine ⟨19894539122802077165639645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53052104327472205775039053 19894539122802077165639645)
                ·
                  refine ⟨7460452171050778937114867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19894539122802077165639645 7460452171050778937114867)
                  ·
                    refine ⟨11190678256576168405672301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7460452171050778937114867 11190678256576168405672301)
                    ·
                      refine ⟨4196504346216063152127113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11190678256576168405672301 4196504346216063152127113)
                      ·
                        rfl

theorem cell23_8172663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 3, 1, 3].length) (baseStart_8172663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172663 prefixEnd_8172663 := by exact prefixLift 8172663
  have htrace : WordTrace (prefixWord ++ tailWord_8172663) baseStart_8172663 baseEnd_8172663 := by
    simpa [prefixWord, tailWord_8172663, baseEnd_8172663] using wordTrace_append hprefix tailTrace_8172663
  have hstable : (prefixWord ++ tailWord_8172663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172663).length < 2 ^ (prefixWord ++ tailWord_8172663).sum := by decide
  have hdescent : baseEnd_8172663 < baseStart_8172663 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172690 : List Nat := [3, 2, 3, 1, 1, 3, 1, 1, 1, 5, 2]
def baseStart_8172690 : Nat := 118140960795 + 8172690 * 2 ^ 59
def prefixEnd_8172690 : Nat := 4983230072969 + 3 ^ 40 * 8172690 * 2
def baseEnd_8172690 : Nat := 4196518210193734546489489

theorem tailTrace_8172690 : CollatzResearch.WordTrace tailWord_8172690 prefixEnd_8172690 4196518210193734546489489 := by
  unfold tailWord_8172690
  simp only [CollatzResearch.WordTrace]
  refine ⟨74520623190436847293260881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198721661841164926115362349 74520623190436847293260881)
  ·
    refine ⟨55890467392827635469945661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74520623190436847293260881 55890467392827635469945661)
    ·
      refine ⟨20958925272310363301229623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55890467392827635469945661 20958925272310363301229623)
      ·
        refine ⟨31438387908465544951844435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20958925272310363301229623 31438387908465544951844435)
        ·
          refine ⟨47157581862698317427766653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31438387908465544951844435 47157581862698317427766653)
          ·
            refine ⟨17684093198511869035412495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47157581862698317427766653 17684093198511869035412495)
            ·
              refine ⟨26526139797767803553118743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17684093198511869035412495 26526139797767803553118743)
              ·
                refine ⟨39789209696651705329678115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26526139797767803553118743 39789209696651705329678115)
                ·
                  refine ⟨59683814544977557994517173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39789209696651705329678115 59683814544977557994517173)
                  ·
                    refine ⟨5595357613591646061985985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59683814544977557994517173 5595357613591646061985985)
                    ·
                      refine ⟨4196518210193734546489489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5595357613591646061985985 4196518210193734546489489)
                      ·
                        rfl

theorem cell23_8172690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_8172690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172690 prefixEnd_8172690 := by exact prefixLift 8172690
  have htrace : WordTrace (prefixWord ++ tailWord_8172690) baseStart_8172690 baseEnd_8172690 := by
    simpa [prefixWord, tailWord_8172690, baseEnd_8172690] using wordTrace_append hprefix tailTrace_8172690
  have hstable : (prefixWord ++ tailWord_8172690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172690).length < 2 ^ (prefixWord ++ tailWord_8172690).sum := by decide
  have hdescent : baseEnd_8172690 < baseStart_8172690 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172700 : List Nat := [2, 2, 3, 2, 1, 2, 4, 1, 1, 5]
def baseStart_8172700 : Nat := 118140960795 + 8172700 * 2 ^ 59
def prefixEnd_8172700 : Nat := 4983230072969 + 3 ^ 40 * 8172700 * 2
def baseEnd_8172700 : Nat := 1398841115000093169121481

theorem tailTrace_8172700 : CollatzResearch.WordTrace tailWord_8172700 prefixEnd_8172700 1398841115000093169121481 := by
  unfold tailWord_8172700
  simp only [CollatzResearch.WordTrace]
  refine ⟨149041428745855580440453777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198721904994474107253938369 149041428745855580440453777)
  ·
    refine ⟨111781071559391685330340333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149041428745855580440453777 111781071559391685330340333)
    ·
      refine ⟨41917901834771881998877625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111781071559391685330340333 41917901834771881998877625)
      ·
        refine ⟨31438426376078911499158219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41917901834771881998877625 31438426376078911499158219)
        ·
          refine ⟨47157639564118367248737329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31438426376078911499158219 47157639564118367248737329)
          ·
            refine ⟨35368229673088775436552997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47157639564118367248737329 35368229673088775436552997)
            ·
              refine ⟨6631543063704145394353687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35368229673088775436552997 6631543063704145394353687)
              ·
                refine ⟨9947314595556218091530531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6631543063704145394353687 9947314595556218091530531)
                ·
                  refine ⟨14920971893334327137295797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9947314595556218091530531 14920971893334327137295797)
                  ·
                    refine ⟨1398841115000093169121481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14920971893334327137295797 1398841115000093169121481)
                    ·
                      rfl

theorem cell23_8172700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_8172700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172700 prefixEnd_8172700 := by exact prefixLift 8172700
  have htrace : WordTrace (prefixWord ++ tailWord_8172700) baseStart_8172700 baseEnd_8172700 := by
    simpa [prefixWord, tailWord_8172700, baseEnd_8172700] using wordTrace_append hprefix tailTrace_8172700
  have hstable : (prefixWord ++ tailWord_8172700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172700).length < 2 ^ (prefixWord ++ tailWord_8172700).sum := by decide
  have hdescent : baseEnd_8172700 < baseStart_8172700 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172714 : List Nat := [3, 1, 5, 1, 1, 1, 2, 4, 1, 1, 3]
def baseStart_8172714 : Nat := 118140960795 + 8172714 * 2 ^ 59
def prefixEnd_8172714 : Nat := 4983230072969 + 3 ^ 40 * 8172714 * 2
def baseEnd_8172714 : Nat := 4196530533729442452589379

theorem tailTrace_8172714 : CollatzResearch.WordTrace tailWord_8172714 prefixEnd_8172714 4196530533729442452589379 := by
  unfold tailWord_8172714
  simp only [CollatzResearch.WordTrace]
  refine ⟨74520842028415110317979299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198722245409106960847944797 74520842028415110317979299)
  ·
    refine ⟨111781263042622665476968949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74520842028415110317979299 111781263042622665476968949)
    ·
      refine ⟨10479493410245874888465839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111781263042622665476968949 10479493410245874888465839)
      ·
        refine ⟨15719240115368812332698759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10479493410245874888465839 15719240115368812332698759)
        ·
          refine ⟨23578860173053218499048139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15719240115368812332698759 23578860173053218499048139)
          ·
            refine ⟨35368290259579827748572209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23578860173053218499048139 35368290259579827748572209)
            ·
              refine ⟨26526217694684870811429157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35368290259579827748572209 26526217694684870811429157)
              ·
                refine ⟨4973665817753413277142967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26526217694684870811429157 4973665817753413277142967)
                ·
                  refine ⟨7460498726630119915714451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4973665817753413277142967 7460498726630119915714451)
                  ·
                    refine ⟨11190748089945179873571677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7460498726630119915714451 11190748089945179873571677)
                    ·
                      refine ⟨4196530533729442452589379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11190748089945179873571677 4196530533729442452589379)
                      ·
                        rfl

theorem cell23_8172714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_8172714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172714 prefixEnd_8172714 := by exact prefixLift 8172714
  have htrace : WordTrace (prefixWord ++ tailWord_8172714) baseStart_8172714 baseEnd_8172714 := by
    simpa [prefixWord, tailWord_8172714, baseEnd_8172714] using wordTrace_append hprefix tailTrace_8172714
  have hstable : (prefixWord ++ tailWord_8172714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172714).length < 2 ^ (prefixWord ++ tailWord_8172714).sum := by decide
  have hdescent : baseEnd_8172714 < baseStart_8172714 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172733 : List Nat := [1, 4, 1, 2, 1, 1, 5, 1, 1, 2, 4]
def baseStart_8172733 : Nat := 118140960795 + 8172733 * 2 ^ 59
def prefixEnd_8172733 : Nat := 4983230072969 + 3 ^ 40 * 8172733 * 2
def baseEnd_8172733 : Nat := 4196540289861877878251791

theorem tailTrace_8172733 : CollatzResearch.WordTrace tailWord_8172733 prefixEnd_8172733 4196540289861877878251791 := by
  unfold tailWord_8172733
  simp only [CollatzResearch.WordTrace]
  refine ⟨298084061100591607516858853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198722707400394405011239235 298084061100591607516858853)
  ·
    refine ⟨55890761456360926409411035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298084061100591607516858853 55890761456360926409411035)
    ·
      refine ⟨83836142184541389614116553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55890761456360926409411035 83836142184541389614116553)
      ·
        refine ⟨62877106638406042210587415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83836142184541389614116553 62877106638406042210587415)
        ·
          refine ⟨94315659957609063315881123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62877106638406042210587415 94315659957609063315881123)
          ·
            refine ⟨141473489936413594973821685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94315659957609063315881123 141473489936413594973821685)
            ·
              refine ⟨13263139681538774528795783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141473489936413594973821685 13263139681538774528795783)
              ·
                refine ⟨19894709522308161793193675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13263139681538774528795783 19894709522308161793193675)
                ·
                  refine ⟨29842064283462242689790513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19894709522308161793193675 29842064283462242689790513)
                  ·
                    refine ⟨22381548212596682017342885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29842064283462242689790513 22381548212596682017342885)
                    ·
                      refine ⟨4196540289861877878251791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22381548212596682017342885 4196540289861877878251791)
                      ·
                        rfl

theorem cell23_8172733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_8172733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172733 prefixEnd_8172733 := by exact prefixLift 8172733
  have htrace : WordTrace (prefixWord ++ tailWord_8172733) baseStart_8172733 baseEnd_8172733 := by
    simpa [prefixWord, tailWord_8172733, baseEnd_8172733] using wordTrace_append hprefix tailTrace_8172733
  have hstable : (prefixWord ++ tailWord_8172733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172733).length < 2 ^ (prefixWord ++ tailWord_8172733).sum := by decide
  have hdescent : baseEnd_8172733 < baseStart_8172733 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172737 : List Nat := [1, 2, 6, 1, 1, 2, 2, 2, 1, 1, 4]
def baseStart_8172737 : Nat := 118140960795 + 8172737 * 2 ^ 59
def prefixEnd_8172737 : Nat := 4983230072969 + 3 ^ 40 * 8172737 * 2
def baseEnd_8172737 : Nat := 4196542343784495862601773

theorem tailTrace_8172737 : CollatzResearch.WordTrace tailWord_8172737 prefixEnd_8172737 4196542343784495862601773 := by
  unfold tailWord_8172737
  simp only [CollatzResearch.WordTrace]
  refine ⟨298084206992577116200004465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198722804661718077466669643 298084206992577116200004465)
  ·
    refine ⟨223563155244432837150003349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298084206992577116200004465 223563155244432837150003349)
    ·
      refine ⟨10479522902082789241406407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 223563155244432837150003349 10479522902082789241406407)
      ·
        refine ⟨15719284353124183862109611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10479522902082789241406407 15719284353124183862109611)
        ·
          refine ⟨23578926529686275793164417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15719284353124183862109611 23578926529686275793164417)
          ·
            refine ⟨17684194897264706844873313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23578926529686275793164417 17684194897264706844873313)
            ·
              refine ⟨13263146172948530133654985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17684194897264706844873313 13263146172948530133654985)
              ·
                refine ⟨9947359629711397600241239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13263146172948530133654985 9947359629711397600241239)
                ·
                  refine ⟨14921039444567096400361859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9947359629711397600241239 14921039444567096400361859)
                  ·
                    refine ⟨22381559166850644600542789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14921039444567096400361859 22381559166850644600542789)
                    ·
                      refine ⟨4196542343784495862601773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22381559166850644600542789 4196542343784495862601773)
                      ·
                        rfl

theorem cell23_8172737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_8172737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172737 prefixEnd_8172737 := by exact prefixLift 8172737
  have htrace : WordTrace (prefixWord ++ tailWord_8172737) baseStart_8172737 baseEnd_8172737 := by
    simpa [prefixWord, tailWord_8172737, baseEnd_8172737] using wordTrace_append hprefix tailTrace_8172737
  have hstable : (prefixWord ++ tailWord_8172737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172737).length < 2 ^ (prefixWord ++ tailWord_8172737).sum := by decide
  have hdescent : baseEnd_8172737 < baseStart_8172737 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172787 : List Nat := [1, 1, 1, 2, 2, 5, 4, 1, 2, 1, 3]
def baseStart_8172787 : Nat := 118140960795 + 8172787 * 2 ^ 59
def prefixEnd_8172787 : Nat := 4983230072969 + 3 ^ 40 * 8172787 * 2
def baseEnd_8172787 : Nat := 4196568017817220666976543

theorem tailTrace_8172787 : CollatzResearch.WordTrace tailWord_8172787 prefixEnd_8172787 4196568017817220666976543 := by
  unfold tailWord_8172787
  simp only [CollatzResearch.WordTrace]
  refine ⟨298086030642395974739324615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198724020428263983159549743 298086030642395974739324615)
  ·
    refine ⟨447129045963593962108986923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298086030642395974739324615 447129045963593962108986923)
    ·
      refine ⟨670693568945390943163480385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447129045963593962108986923 670693568945390943163480385)
      ·
        refine ⟨503020176709043207372610289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 670693568945390943163480385 503020176709043207372610289)
        ·
          refine ⟨377265132531782405529457717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 503020176709043207372610289 377265132531782405529457717)
          ·
            refine ⟨35368606174854600518386661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 377265132531782405529457717 35368606174854600518386661)
            ·
              refine ⟨6631613657785237597197499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35368606174854600518386661 6631613657785237597197499)
              ·
                refine ⟨9947420486677856395796249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6631613657785237597197499 9947420486677856395796249)
                ·
                  refine ⟨7460565365008392296847187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9947420486677856395796249 7460565365008392296847187)
                  ·
                    refine ⟨11190848047512588445270781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7460565365008392296847187 11190848047512588445270781)
                    ·
                      refine ⟨4196568017817220666976543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11190848047512588445270781 4196568017817220666976543)
                      ·
                        rfl

theorem cell23_8172787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 1, 2, 1, 3].length) (baseStart_8172787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172787 prefixEnd_8172787 := by exact prefixLift 8172787
  have htrace : WordTrace (prefixWord ++ tailWord_8172787) baseStart_8172787 baseEnd_8172787 := by
    simpa [prefixWord, tailWord_8172787, baseEnd_8172787] using wordTrace_append hprefix tailTrace_8172787
  have hstable : (prefixWord ++ tailWord_8172787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172787).length < 2 ^ (prefixWord ++ tailWord_8172787).sum := by decide
  have hdescent : baseEnd_8172787 < baseStart_8172787 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172788 : List Nat := [2, 6, 1, 2, 2, 1, 1, 2, 1, 1, 4]
def baseStart_8172788 : Nat := 118140960795 + 8172788 * 2 ^ 59
def prefixEnd_8172788 : Nat := 4983230072969 + 3 ^ 40 * 8172788 * 2
def baseEnd_8172788 : Nat := 4196568531297875163064039

theorem tailTrace_8172788 : CollatzResearch.WordTrace tailWord_8172788 prefixEnd_8172788 4196568531297875163064039 := by
  unfold tailWord_8172788
  simp only [CollatzResearch.WordTrace]
  refine ⟨149043033557696175955055509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198724044743594901273407345 149043033557696175955055509)
  ·
    refine ⟨6986392198017008247893227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 149043033557696175955055509 6986392198017008247893227)
    ·
      refine ⟨10479588297025512371839841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6986392198017008247893227 10479588297025512371839841)
      ·
        refine ⟨7859691222769134278879881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10479588297025512371839841 7859691222769134278879881)
        ·
          refine ⟨5894768417076850709159911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7859691222769134278879881 5894768417076850709159911)
          ·
            refine ⟨8842152625615276063739867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5894768417076850709159911 8842152625615276063739867)
            ·
              refine ⟨13263228938422914095609801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8842152625615276063739867 13263228938422914095609801)
              ·
                refine ⟨9947421703817185571707351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13263228938422914095609801 9947421703817185571707351)
                ·
                  refine ⟨14921132555725778357561027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9947421703817185571707351 14921132555725778357561027)
                  ·
                    refine ⟨22381698833588667536341541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14921132555725778357561027 22381698833588667536341541)
                    ·
                      refine ⟨4196568531297875163064039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22381698833588667536341541 4196568531297875163064039)
                      ·
                        rfl

theorem cell23_8172788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_8172788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172788 prefixEnd_8172788 := by exact prefixLift 8172788
  have htrace : WordTrace (prefixWord ++ tailWord_8172788) baseStart_8172788 baseEnd_8172788 := by
    simpa [prefixWord, tailWord_8172788, baseEnd_8172788] using wordTrace_append hprefix tailTrace_8172788
  have hstable : (prefixWord ++ tailWord_8172788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172788).length < 2 ^ (prefixWord ++ tailWord_8172788).sum := by decide
  have hdescent : baseEnd_8172788 < baseStart_8172788 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172814 : List Nat := [4, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2]
def baseStart_8172814 : Nat := 118140960795 + 8172814 * 2 ^ 59
def prefixEnd_8172814 : Nat := 4983230072969 + 3 ^ 40 * 8172814 * 2
def baseEnd_8172814 : Nat := 4196581881794892061338919

theorem tailTrace_8172814 : CollatzResearch.WordTrace tailWord_8172814 prefixEnd_8172814 4196581881794892061338919 := by
  unfold tailWord_8172814
  simp only [CollatzResearch.WordTrace]
  refine ⟨37260876926662269793819687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198724676942198772233704997 37260876926662269793819687)
  ·
    refine ⟨55891315389993404690729531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37260876926662269793819687 55891315389993404690729531)
    ·
      refine ⟨83836973084990107036094297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55891315389993404690729531 83836973084990107036094297)
      ·
        refine ⟨62877729813742580277070723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83836973084990107036094297 62877729813742580277070723)
        ·
          refine ⟨94316594720613870415606085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62877729813742580277070723 94316594720613870415606085)
          ·
            refine ⟨17684361510115100702926141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94316594720613870415606085 17684361510115100702926141)
            ·
              refine ⟨6631635566293162763597303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17684361510115100702926141 6631635566293162763597303)
              ·
                refine ⟨9947453349439744145395955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6631635566293162763597303 9947453349439744145395955)
                ·
                  refine ⟨14921180024159616218093933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9947453349439744145395955 14921180024159616218093933)
                  ·
                    refine ⟨5595442509059856081785225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14921180024159616218093933 5595442509059856081785225)
                    ·
                      refine ⟨4196581881794892061338919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5595442509059856081785225 4196581881794892061338919)
                      ·
                        rfl

theorem cell23_8172814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2].length) (baseStart_8172814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172814 prefixEnd_8172814 := by exact prefixLift 8172814
  have htrace : WordTrace (prefixWord ++ tailWord_8172814) baseStart_8172814 baseEnd_8172814 := by
    simpa [prefixWord, tailWord_8172814, baseEnd_8172814] using wordTrace_append hprefix tailTrace_8172814
  have hstable : (prefixWord ++ tailWord_8172814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172814).length < 2 ^ (prefixWord ++ tailWord_8172814).sum := by decide
  have hdescent : baseEnd_8172814 < baseStart_8172814 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172823 : List Nat := [1, 1, 3, 4, 1, 1, 2, 2, 2, 2, 4]
def baseStart_8172823 : Nat := 118140960795 + 8172823 * 2 ^ 59
def prefixEnd_8172823 : Nat := 4983230072969 + 3 ^ 40 * 8172823 * 2
def baseEnd_8172823 : Nat := 4196586503120782526126377

theorem tailTrace_8172823 : CollatzResearch.WordTrace tailWord_8172823 prefixEnd_8172823 4196586503120782526126377 := by
  unfold tailWord_8172823
  simp only [CollatzResearch.WordTrace]
  refine ⟨298087343670265552887635123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198724895780177035258423415 298087343670265552887635123)
  ·
    refine ⟨447131015505398329331452685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298087343670265552887635123 447131015505398329331452685)
    ·
      refine ⟨167674130814524373499294757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 447131015505398329331452685 167674130814524373499294757)
      ·
        refine ⟨31438899527723320031117767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167674130814524373499294757 31438899527723320031117767)
        ·
          refine ⟨47158349291584980046676651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31438899527723320031117767 47158349291584980046676651)
          ·
            refine ⟨70737523937377470070014977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47158349291584980046676651 70737523937377470070014977)
            ·
              refine ⟨53053142953033102552511233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70737523937377470070014977 53053142953033102552511233)
              ·
                refine ⟨39789857214774826914383425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53053142953033102552511233 39789857214774826914383425)
                ·
                  refine ⟨29842392911081120185787569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39789857214774826914383425 29842392911081120185787569)
                  ·
                    refine ⟨22381794683310840139340677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29842392911081120185787569 22381794683310840139340677)
                    ·
                      refine ⟨4196586503120782526126377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22381794683310840139340677 4196586503120782526126377)
                      ·
                        rfl

theorem cell23_8172823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_8172823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172823 prefixEnd_8172823 := by exact prefixLift 8172823
  have htrace : WordTrace (prefixWord ++ tailWord_8172823) baseStart_8172823 baseEnd_8172823 := by
    simpa [prefixWord, tailWord_8172823, baseEnd_8172823] using wordTrace_append hprefix tailTrace_8172823
  have hstable : (prefixWord ++ tailWord_8172823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172823).length < 2 ^ (prefixWord ++ tailWord_8172823).sum := by decide
  have hdescent : baseEnd_8172823 < baseStart_8172823 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172840 : List Nat := [2, 1, 5, 1, 2, 2, 1, 1, 2, 2, 4]
def baseStart_8172840 : Nat := 118140960795 + 8172840 * 2 ^ 59
def prefixEnd_8172840 : Nat := 4983230072969 + 3 ^ 40 * 8172840 * 2
def baseEnd_8172840 : Nat := 4196595232291908959613799

theorem tailTrace_8172840 : CollatzResearch.WordTrace tailWord_8172840 prefixEnd_8172840 4196595232291908959613799 := by
  unfold tailWord_8172840
  simp only [CollatzResearch.WordTrace]
  refine ⟨149043981855601982395501987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198725309140802643194002649 149043981855601982395501987)
  ·
    refine ⟨223565972783402973593252981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149043981855601982395501987 223565972783402973593252981)
    ·
      refine ⟨20959309948444028774367467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 223565972783402973593252981 20959309948444028774367467)
      ·
        refine ⟨31438964922666043161551201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20959309948444028774367467 31438964922666043161551201)
        ·
          refine ⟨23579223691999532371163401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31438964922666043161551201 23579223691999532371163401)
          ·
            refine ⟨17684417768999649278372551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23579223691999532371163401 17684417768999649278372551)
            ·
              refine ⟨26526626653499473917558827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17684417768999649278372551 26526626653499473917558827)
              ·
                refine ⟨39789939980249210876338241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26526626653499473917558827 39789939980249210876338241)
                ·
                  refine ⟨29842454985186908157253681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39789939980249210876338241 29842454985186908157253681)
                  ·
                    refine ⟨22381841238890181117940261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29842454985186908157253681 22381841238890181117940261)
                    ·
                      refine ⟨4196595232291908959613799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22381841238890181117940261 4196595232291908959613799)
                      ·
                        rfl

theorem cell23_8172840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_8172840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172840 prefixEnd_8172840 := by exact prefixLift 8172840
  have htrace : WordTrace (prefixWord ++ tailWord_8172840) baseStart_8172840 baseEnd_8172840 := by
    simpa [prefixWord, tailWord_8172840, baseEnd_8172840] using wordTrace_append hprefix tailTrace_8172840
  have hstable : (prefixWord ++ tailWord_8172840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172840).length < 2 ^ (prefixWord ++ tailWord_8172840).sum := by decide
  have hdescent : baseEnd_8172840 < baseStart_8172840 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172863 : List Nat := [1, 1, 2, 2, 4, 3, 1, 1, 1, 7]
def baseStart_8172863 : Nat := 118140960795 + 8172863 * 2 ^ 59
def prefixEnd_8172863 : Nat := 4983230072969 + 3 ^ 40 * 8172863 * 2
def baseEnd_8172863 : Nat := 1398869014115654123208731

theorem tailTrace_8172863 : CollatzResearch.WordTrace tailWord_8172863 prefixEnd_8172863 1398869014115654123208731 := by
  unfold tailWord_8172863
  simp only [CollatzResearch.WordTrace]
  refine ⟨298088802590120639719091243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198725868393413759812727495 298088802590120639719091243)
  ·
    refine ⟨447133203885180959578636865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298088802590120639719091243 447133203885180959578636865)
    ·
      refine ⟨335349902913885719683977649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447133203885180959578636865 335349902913885719683977649)
      ·
        refine ⟨251512427185414289762983237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335349902913885719683977649 251512427185414289762983237)
        ·
          refine ⟨47158580097265179330559357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 251512427185414289762983237 47158580097265179330559357)
          ·
            refine ⟨17684467536474442248959759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47158580097265179330559357 17684467536474442248959759)
            ·
              refine ⟨26526701304711663373439639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17684467536474442248959759 26526701304711663373439639)
              ·
                refine ⟨39790051957067495060159459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26526701304711663373439639 39790051957067495060159459)
                ·
                  refine ⟨59685077935601242590239189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39790051957067495060159459 59685077935601242590239189)
                  ·
                    refine ⟨1398869014115654123208731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59685077935601242590239189 1398869014115654123208731)
                    ·
                      rfl

theorem cell23_8172863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 7].length) (baseStart_8172863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172863 prefixEnd_8172863 := by exact prefixLift 8172863
  have htrace : WordTrace (prefixWord ++ tailWord_8172863) baseStart_8172863 baseEnd_8172863 := by
    simpa [prefixWord, tailWord_8172863, baseEnd_8172863] using wordTrace_append hprefix tailTrace_8172863
  have hstable : (prefixWord ++ tailWord_8172863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172863).length < 2 ^ (prefixWord ++ tailWord_8172863).sum := by decide
  have hdescent : baseEnd_8172863 < baseStart_8172863 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172883 : List Nat := [1, 1, 1, 2, 1, 1, 6, 1, 4, 1, 4]
def baseStart_8172883 : Nat := 118140960795 + 8172883 * 2 ^ 59
def prefixEnd_8172883 : Nat := 4983230072969 + 3 ^ 40 * 8172883 * 2
def baseEnd_8172883 : Nat := 4196617311960052291376101

theorem tailTrace_8172883 : CollatzResearch.WordTrace tailWord_8172883 prefixEnd_8172883 4196617311960052291376101 := by
  unfold tailWord_8172883
  simp only [CollatzResearch.WordTrace]
  refine ⟨298089532050048183134819303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198726354700032122089879535 298089532050048183134819303)
  ·
    refine ⟨447134298075072274702228955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298089532050048183134819303 447134298075072274702228955)
    ·
      refine ⟨670701447112608412053343433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447134298075072274702228955 670701447112608412053343433)
      ·
        refine ⟨503026085334456309040007575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 670701447112608412053343433 503026085334456309040007575)
        ·
          refine ⟨754539128001684463560011363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503026085334456309040007575 754539128001684463560011363)
          ·
            refine ⟨1131808692002526695340017045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754539128001684463560011363 1131808692002526695340017045)
            ·
              refine ⟨53053532437618438844063299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1131808692002526695340017045 53053532437618438844063299)
              ·
                refine ⟨79580298656427658266094949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53053532437618438844063299 79580298656427658266094949)
                ·
                  refine ⟨14921305998080185924892803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79580298656427658266094949 14921305998080185924892803)
                  ·
                    refine ⟨22381958997120278887339205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14921305998080185924892803 22381958997120278887339205)
                    ·
                      refine ⟨4196617311960052291376101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22381958997120278887339205 4196617311960052291376101)
                      ·
                        rfl

theorem cell23_8172883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4, 1, 4].length) (baseStart_8172883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172883 prefixEnd_8172883 := by exact prefixLift 8172883
  have htrace : WordTrace (prefixWord ++ tailWord_8172883) baseStart_8172883 baseEnd_8172883 := by
    simpa [prefixWord, tailWord_8172883, baseEnd_8172883] using wordTrace_append hprefix tailTrace_8172883
  have hstable : (prefixWord ++ tailWord_8172883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172883).length < 2 ^ (prefixWord ++ tailWord_8172883).sum := by decide
  have hdescent : baseEnd_8172883 < baseStart_8172883 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172937 : List Nat := [1, 2, 1, 1, 7, 1, 1, 2, 2, 2, 3]
def baseStart_8172937 : Nat := 118140960795 + 8172937 * 2 ^ 59
def prefixEnd_8172937 : Nat := 4983230072969 + 3 ^ 40 * 8172937 * 2
def baseEnd_8172937 : Nat := 4196645039915395080100853

theorem tailTrace_8172937 : CollatzResearch.WordTrace tailWord_8172937 prefixEnd_8172937 4196645039915395080100853 := by
  unfold tailWord_8172937
  simp only [CollatzResearch.WordTrace]
  refine ⟨298091501591852550357285065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198727667727901700238190043 298091501591852550357285065)
  ·
    refine ⟨223568626193889412767963799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298091501591852550357285065 223568626193889412767963799)
    ·
      refine ⟨335352939290834119151945699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223568626193889412767963799 335352939290834119151945699)
      ·
        refine ⟨503029408936251178727918549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335352939290834119151945699 503029408936251178727918549)
        ·
          refine ⟨11789751771943387001435591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 503029408936251178727918549 11789751771943387001435591)
          ·
            refine ⟨17684627657915080502153387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11789751771943387001435591 17684627657915080502153387)
            ·
              refine ⟨26526941486872620753230081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17684627657915080502153387 26526941486872620753230081)
              ·
                refine ⟨19895206115154465564922561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26526941486872620753230081 19895206115154465564922561)
                ·
                  refine ⟨14921404586365849173691921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19895206115154465564922561 14921404586365849173691921)
                  ·
                    refine ⟨11191053439774386880268941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14921404586365849173691921 11191053439774386880268941)
                    ·
                      refine ⟨4196645039915395080100853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11191053439774386880268941 4196645039915395080100853)
                      ·
                        rfl

theorem cell23_8172937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 2, 2, 3].length) (baseStart_8172937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172937 prefixEnd_8172937 := by exact prefixLift 8172937
  have htrace : WordTrace (prefixWord ++ tailWord_8172937) baseStart_8172937 baseEnd_8172937 := by
    simpa [prefixWord, tailWord_8172937, baseEnd_8172937] using wordTrace_append hprefix tailTrace_8172937
  have hstable : (prefixWord ++ tailWord_8172937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172937).length < 2 ^ (prefixWord ++ tailWord_8172937).sum := by decide
  have hdescent : baseEnd_8172937 < baseStart_8172937 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172957 : List Nat := [1, 4, 2, 1, 3, 1, 4, 1, 6]
def baseStart_8172957 : Nat := 118140960795 + 8172957 * 2 ^ 59
def prefixEnd_8172957 : Nat := 4983230072969 + 3 ^ 40 * 8172957 * 2
def baseEnd_8172957 : Nat := 466295034392053889094529

theorem tailTrace_8172957 : CollatzResearch.WordTrace tailWord_8172957 prefixEnd_8172957 466295034392053889094529 := by
  unfold tailWord_8172957
  simp only [CollatzResearch.WordTrace]
  refine ⟨298092231051780093773013125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198728154034520062515342083 298092231051780093773013125)
  ·
    refine ⟨55892293322208767582439961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298092231051780093773013125 55892293322208767582439961)
    ·
      refine ⟨41919219991656575686829971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55892293322208767582439961 41919219991656575686829971)
      ·
        refine ⟨62878829987484863530244957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41919219991656575686829971 62878829987484863530244957)
        ·
          refine ⟨23579561245306823823841859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62878829987484863530244957 23579561245306823823841859)
          ·
            refine ⟨35369341867960235735762789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23579561245306823823841859 35369341867960235735762789)
            ·
              refine ⟨6631751600242544200455523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35369341867960235735762789 6631751600242544200455523)
              ·
                refine ⟨9947627400363816300683285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6631751600242544200455523 9947627400363816300683285)
                ·
                  refine ⟨466295034392053889094529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9947627400363816300683285 466295034392053889094529)
                  ·
                    rfl

theorem cell23_8172957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 1, 6].length) (baseStart_8172957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172957 prefixEnd_8172957 := by exact prefixLift 8172957
  have htrace : WordTrace (prefixWord ++ tailWord_8172957) baseStart_8172957 baseEnd_8172957 := by
    simpa [prefixWord, tailWord_8172957, baseEnd_8172957] using wordTrace_append hprefix tailTrace_8172957
  have hstable : (prefixWord ++ tailWord_8172957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172957).length < 2 ^ (prefixWord ++ tailWord_8172957).sum := by decide
  have hdescent : baseEnd_8172957 < baseStart_8172957 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8172967 : List Nat := [1, 1, 6, 1, 1, 1, 2, 1, 5, 1, 3]
def baseStart_8172967 : Nat := 118140960795 + 8172967 * 2 ^ 59
def prefixEnd_8172967 : Nat := 4983230072969 + 3 ^ 40 * 8172967 * 2
def baseEnd_8172967 : Nat := 4196660444335029962725715

theorem tailTrace_8172967 : CollatzResearch.WordTrace tailWord_8172967 prefixEnd_8172967 4196660444335029962725715 := by
  unfold tailWord_8172967
  simp only [CollatzResearch.WordTrace]
  refine ⟨298092595781743865480877155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198728397187829243653918103 298092595781743865480877155)
  ·
    refine ⟨447138893672615798221315733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298092595781743865480877155 447138893672615798221315733)
    ·
      refine ⟨20959635640903865541624175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 447138893672615798221315733 20959635640903865541624175)
      ·
        refine ⟨31439453461355798312436263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20959635640903865541624175 31439453461355798312436263)
        ·
          refine ⟨47159180192033697468654395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31439453461355798312436263 47159180192033697468654395)
          ·
            refine ⟨70738770288050546202981593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47159180192033697468654395 70738770288050546202981593)
            ·
              refine ⟨53054077716037909652236195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70738770288050546202981593 53054077716037909652236195)
              ·
                refine ⟨79581116574056864478354293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53054077716037909652236195 79581116574056864478354293)
                ·
                  refine ⟨7460729678817831044845715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79581116574056864478354293 7460729678817831044845715)
                  ·
                    refine ⟨11191094518226746567268573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7460729678817831044845715 11191094518226746567268573)
                    ·
                      refine ⟨4196660444335029962725715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11191094518226746567268573 4196660444335029962725715)
                      ·
                        rfl

theorem cell23_8172967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_8172967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8172967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8172967 prefixEnd_8172967 := by exact prefixLift 8172967
  have htrace : WordTrace (prefixWord ++ tailWord_8172967) baseStart_8172967 baseEnd_8172967 := by
    simpa [prefixWord, tailWord_8172967, baseEnd_8172967] using wordTrace_append hprefix tailTrace_8172967
  have hstable : (prefixWord ++ tailWord_8172967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8172967).length < 2 ^ (prefixWord ++ tailWord_8172967).sum := by decide
  have hdescent : baseEnd_8172967 < baseStart_8172967 := by decide
  rcases family_descends (prefixWord ++ tailWord_8172967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173003 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 6]
def baseStart_8173003 : Nat := 118140960795 + 8173003 * 2 ^ 59
def prefixEnd_8173003 : Nat := 4983230072969 + 3 ^ 40 * 8173003 * 2
def baseEnd_8173003 : Nat := 4196678929638591821875549

theorem tailTrace_8173003 : CollatzResearch.WordTrace tailWord_8173003 prefixEnd_8173003 4196678929638591821875549 := by
  unfold tailWord_8173003
  simp only [CollatzResearch.WordTrace]
  refine ⟨298093908809613443629187663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198729272539742295752791775 298093908809613443629187663)
  ·
    refine ⟨447140863214420165443781495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298093908809613443629187663 447140863214420165443781495)
    ·
      refine ⟨670711294821630248165672243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447140863214420165443781495 670711294821630248165672243)
      ·
        refine ⟨1006066942232445372248508365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 670711294821630248165672243 1006066942232445372248508365)
        ·
          refine ⟨377275103337167014593190637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1006066942232445372248508365 377275103337167014593190637)
          ·
            refine ⟨141478163751437630472446489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 377275103337167014593190637 141478163751437630472446489)
            ·
              refine ⟨106108622813578222854334867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141478163751437630472446489 106108622813578222854334867)
              ·
                refine ⟨159162934220367334281502301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106108622813578222854334867 159162934220367334281502301)
                ·
                  refine ⟨59686100332637750355563363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159162934220367334281502301 59686100332637750355563363)
                  ·
                    refine ⟨89529150498956625533345045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59686100332637750355563363 89529150498956625533345045)
                    ·
                      refine ⟨4196678929638591821875549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89529150498956625533345045 4196678929638591821875549)
                      ·
                        rfl

theorem cell23_8173003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 6].length) (baseStart_8173003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173003 prefixEnd_8173003 := by exact prefixLift 8173003
  have htrace : WordTrace (prefixWord ++ tailWord_8173003) baseStart_8173003 baseEnd_8173003 := by
    simpa [prefixWord, tailWord_8173003, baseEnd_8173003] using wordTrace_append hprefix tailTrace_8173003
  have hstable : (prefixWord ++ tailWord_8173003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173003).length < 2 ^ (prefixWord ++ tailWord_8173003).sum := by decide
  have hdescent : baseEnd_8173003 < baseStart_8173003 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173017 : List Nat := [1, 2, 1, 2, 4, 2, 2, 3, 2, 4]
def baseStart_8173017 : Nat := 118140960795 + 8173017 * 2 ^ 59
def prefixEnd_8173017 : Nat := 4983230072969 + 3 ^ 40 * 8173017 * 2
def baseEnd_8173017 : Nat := 1398895372789251589033495

theorem tailTrace_8173017 : CollatzResearch.WordTrace tailWord_8173017 prefixEnd_8173017 1398895372789251589033495 := by
  unfold tailWord_8173017
  simp only [CollatzResearch.WordTrace]
  refine ⟨298094419431562724020197305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198729612954375149346798203 298094419431562724020197305)
  ·
    refine ⟨223570814573672043015147979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298094419431562724020197305 223570814573672043015147979)
    ·
      refine ⟨335356221860508064522721969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223570814573672043015147979 335356221860508064522721969)
      ·
        refine ⟨251517166395381048392041477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335356221860508064522721969 251517166395381048392041477)
        ·
          refine ⟨47159468699133946573507777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 251517166395381048392041477 47159468699133946573507777)
          ·
            refine ⟨35369601524350459930130833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47159468699133946573507777 35369601524350459930130833)
            ·
              refine ⟨26527201143262844947598125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35369601524350459930130833 26527201143262844947598125)
              ·
                refine ⟨9947700428723566855349297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26527201143262844947598125 9947700428723566855349297)
                ·
                  refine ⟨7460775321542675141511973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9947700428723566855349297 7460775321542675141511973)
                  ·
                    refine ⟨1398895372789251589033495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7460775321542675141511973 1398895372789251589033495)
                    ·
                      rfl

theorem cell23_8173017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3, 2, 4].length) (baseStart_8173017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173017 prefixEnd_8173017 := by exact prefixLift 8173017
  have htrace : WordTrace (prefixWord ++ tailWord_8173017) baseStart_8173017 baseEnd_8173017 := by
    simpa [prefixWord, tailWord_8173017, baseEnd_8173017] using wordTrace_append hprefix tailTrace_8173017
  have hstable : (prefixWord ++ tailWord_8173017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173017).length < 2 ^ (prefixWord ++ tailWord_8173017).sum := by decide
  have hdescent : baseEnd_8173017 < baseStart_8173017 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173027 : List Nat := [1, 1, 1, 6, 2, 1, 2, 1, 3, 2, 3]
def baseStart_8173027 : Nat := 118140960795 + 8173027 * 2 ^ 59
def prefixEnd_8173027 : Nat := 4983230072969 + 3 ^ 40 * 8173027 * 2
def baseEnd_8173027 : Nat := 4196691253174299727975439

theorem tailTrace_8173027 : CollatzResearch.WordTrace tailWord_8173027 prefixEnd_8173027 4196691253174299727975439 := by
  unfold tailWord_8173027
  simp only [CollatzResearch.WordTrace]
  refine ⟨298094784161526495728061335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198729856107684330485374223 298094784161526495728061335)
  ·
    refine ⟨447142176242289743592092003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298094784161526495728061335 447142176242289743592092003)
    ·
      refine ⟨670713264363434615388138005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447142176242289743592092003 670713264363434615388138005)
      ·
        refine ⟨31439684267035997596318969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 670713264363434615388138005 31439684267035997596318969)
        ·
          refine ⟨23579763200276998197239227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31439684267035997596318969 23579763200276998197239227)
          ·
            refine ⟨35369644800415497295858841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23579763200276998197239227 35369644800415497295858841)
            ·
              refine ⟨26527233600311622971894131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35369644800415497295858841 26527233600311622971894131)
              ·
                refine ⟨39790850400467434457841197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26527233600311622971894131 39790850400467434457841197)
                ·
                  refine ⟨14921568900175287921690449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39790850400467434457841197 14921568900175287921690449)
                  ·
                    refine ⟨11191176675131465941267837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14921568900175287921690449 11191176675131465941267837)
                    ·
                      refine ⟨4196691253174299727975439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11191176675131465941267837 4196691253174299727975439)
                      ·
                        rfl

theorem cell23_8173027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_8173027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173027 prefixEnd_8173027 := by exact prefixLift 8173027
  have htrace : WordTrace (prefixWord ++ tailWord_8173027) baseStart_8173027 baseEnd_8173027 := by
    simpa [prefixWord, tailWord_8173027, baseEnd_8173027] using wordTrace_append hprefix tailTrace_8173027
  have hstable : (prefixWord ++ tailWord_8173027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173027).length < 2 ^ (prefixWord ++ tailWord_8173027).sum := by decide
  have hdescent : baseEnd_8173027 < baseStart_8173027 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173033 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 4, 2, 6]
def baseStart_8173033 : Nat := 118140960795 + 8173033 * 2 ^ 59
def prefixEnd_8173033 : Nat := 4983230072969 + 3 ^ 40 * 8173033 * 2
def baseEnd_8173033 : Nat := 4196694334058226704500411

theorem tailTrace_8173033 : CollatzResearch.WordTrace tailWord_8173033 prefixEnd_8173033 4196694334058226704500411 := by
  unfold tailWord_8173033
  simp only [CollatzResearch.WordTrace]
  refine ⟨298095002999504758752779753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198730001999669839168519835 298095002999504758752779753)
  ·
    refine ⟨223571252249628569064584815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298095002999504758752779753 223571252249628569064584815)
    ·
      refine ⟨335356878374442853596877223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223571252249628569064584815 335356878374442853596877223)
      ·
        refine ⟨503035317561664280395315835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335356878374442853596877223 503035317561664280395315835)
        ·
          refine ⟨754552976342496420592973753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503035317561664280395315835 754552976342496420592973753)
          ·
            refine ⟨565914732256872315444730315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 754552976342496420592973753 565914732256872315444730315)
            ·
              refine ⟨848872098385308473167095473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 565914732256872315444730315 848872098385308473167095473)
              ·
                refine ⟨636654073788981354875321605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 848872098385308473167095473 636654073788981354875321605)
                ·
                  refine ⟨119372638835434004039122801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 636654073788981354875321605 119372638835434004039122801)
                  ·
                    refine ⟨89529479126575503029342101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 119372638835434004039122801 89529479126575503029342101)
                    ·
                      refine ⟨4196694334058226704500411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89529479126575503029342101 4196694334058226704500411)
                      ·
                        rfl

theorem cell23_8173033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 2, 6].length) (baseStart_8173033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173033 prefixEnd_8173033 := by exact prefixLift 8173033
  have htrace : WordTrace (prefixWord ++ tailWord_8173033) baseStart_8173033 baseEnd_8173033 := by
    simpa [prefixWord, tailWord_8173033, baseEnd_8173033] using wordTrace_append hprefix tailTrace_8173033
  have hstable : (prefixWord ++ tailWord_8173033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173033).length < 2 ^ (prefixWord ++ tailWord_8173033).sum := by decide
  have hdescent : baseEnd_8173033 < baseStart_8173033 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173041 : List Nat := [1, 2, 2, 2, 3, 2, 1, 5, 1, 2, 2]
def baseStart_8173041 : Nat := 118140960795 + 8173041 * 2 ^ 59
def prefixEnd_8173041 : Nat := 4983230072969 + 3 ^ 40 * 8173041 * 2
def baseEnd_8173041 : Nat := 4196698441903462673200375

theorem tailTrace_8173041 : CollatzResearch.WordTrace tailWord_8173041 prefixEnd_8173041 4196698441903462673200375 := by
  unfold tailWord_8173041
  simp only [CollatzResearch.WordTrace]
  refine ⟨298095294783475776119070977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198730196522317184079380651 298095294783475776119070977)
  ·
    refine ⟨223571471087606832089303233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298095294783475776119070977 223571471087606832089303233)
    ·
      refine ⟨167678603315705124066977425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223571471087606832089303233 167678603315705124066977425)
      ·
        refine ⟨125758952486778843050233069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167678603315705124066977425 125758952486778843050233069)
        ·
          refine ⟨47159607182542066143837401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125758952486778843050233069 47159607182542066143837401)
          ·
            refine ⟨35369705386906549607878051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47159607182542066143837401 35369705386906549607878051)
            ·
              refine ⟨53054558080359824411817077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35369705386906549607878051 53054558080359824411817077)
              ·
                refine ⟨4973864820033733538607851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53054558080359824411817077 4973864820033733538607851)
                ·
                  refine ⟨7460797230050600307911777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4973864820033733538607851 7460797230050600307911777)
                  ·
                    refine ⟨5595597922537950230933833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7460797230050600307911777 5595597922537950230933833)
                    ·
                      refine ⟨4196698441903462673200375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5595597922537950230933833 4196698441903462673200375)
                      ·
                        rfl

theorem cell23_8173041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 5, 1, 2, 2].length) (baseStart_8173041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173041 prefixEnd_8173041 := by exact prefixLift 8173041
  have htrace : WordTrace (prefixWord ++ tailWord_8173041) baseStart_8173041 baseEnd_8173041 := by
    simpa [prefixWord, tailWord_8173041, baseEnd_8173041] using wordTrace_append hprefix tailTrace_8173041
  have hstable : (prefixWord ++ tailWord_8173041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173041).length < 2 ^ (prefixWord ++ tailWord_8173041).sum := by decide
  have hdescent : baseEnd_8173041 < baseStart_8173041 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173043 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 1, 9]
def baseStart_8173043 : Nat := 118140960795 + 8173043 * 2 ^ 59
def prefixEnd_8173043 : Nat := 4983230072969 + 3 ^ 40 * 8173043 * 2
def baseEnd_8173043 : Nat := 1398899822954923888458455

theorem tailTrace_8173043 : CollatzResearch.WordTrace tailWord_8173043 prefixEnd_8173043 1398899822954923888458455 := by
  unfold tailWord_8173043
  simp only [CollatzResearch.WordTrace]
  refine ⟨298095367729468530460643783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198730245152979020307095855 298095367729468530460643783)
  ·
    refine ⟨447143051594202795690965675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298095367729468530460643783 447143051594202795690965675)
    ·
      refine ⟨670714577391304193536448513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447143051594202795690965675 670714577391304193536448513)
      ·
        refine ⟨503035933043478145152336385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 670714577391304193536448513 503035933043478145152336385)
        ·
          refine ⟨377276949782608608864252289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 503035933043478145152336385 377276949782608608864252289)
          ·
            refine ⟨282957712336956456648189217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377276949782608608864252289 282957712336956456648189217)
            ·
              refine ⟨212218284252717342486141913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282957712336956456648189217 212218284252717342486141913)
              ·
                refine ⟨159163713189538006864606435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212218284252717342486141913 159163713189538006864606435)
                ·
                  refine ⟨238745569784307010296909653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159163713189538006864606435 238745569784307010296909653)
                  ·
                    refine ⟨1398899822954923888458455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 238745569784307010296909653 1398899822954923888458455)
                    ·
                      rfl

theorem cell23_8173043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 9].length) (baseStart_8173043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173043 prefixEnd_8173043 := by exact prefixLift 8173043
  have htrace : WordTrace (prefixWord ++ tailWord_8173043) baseStart_8173043 baseEnd_8173043 := by
    simpa [prefixWord, tailWord_8173043, baseEnd_8173043] using wordTrace_append hprefix tailTrace_8173043
  have hstable : (prefixWord ++ tailWord_8173043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173043).length < 2 ^ (prefixWord ++ tailWord_8173043).sum := by decide
  have hdescent : baseEnd_8173043 < baseStart_8173043 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173058 : List Nat := [3, 4, 1, 2, 1, 2, 2, 1, 3, 2, 2]
def baseStart_8173058 : Nat := 118140960795 + 8173058 * 2 ^ 59
def prefixEnd_8173058 : Nat := 4983230072969 + 3 ^ 40 * 8173058 * 2
def baseEnd_8173058 : Nat := 4196707171074589106687797

theorem tailTrace_8173058 : CollatzResearch.WordTrace tailWord_8173058 prefixEnd_8173058 4196707171074589106687797 := by
  unfold tailWord_8173058
  simp only [CollatzResearch.WordTrace]
  refine ⟨74523978706103547005609957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198730609882942792014959885 74523978706103547005609957)
  ·
    refine ⟨13973246007394415063551867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74523978706103547005609957 13973246007394415063551867)
    ·
      refine ⟨20959869011091622595327801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13973246007394415063551867 20959869011091622595327801)
      ·
        refine ⟨15719901758318716946495851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20959869011091622595327801 15719901758318716946495851)
        ·
          refine ⟨23579852637478075419743777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15719901758318716946495851 23579852637478075419743777)
          ·
            refine ⟨17684889478108556564807833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23579852637478075419743777 17684889478108556564807833)
            ·
              refine ⟨13263667108581417423605875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17684889478108556564807833 13263667108581417423605875)
              ·
                refine ⟨19895500662872126135408813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13263667108581417423605875 19895500662872126135408813)
                ·
                  refine ⟨7460812748577047300778305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19895500662872126135408813 7460812748577047300778305)
                  ·
                    refine ⟨5595609561432785475583729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7460812748577047300778305 5595609561432785475583729)
                    ·
                      refine ⟨4196707171074589106687797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5595609561432785475583729 4196707171074589106687797)
                      ·
                        rfl

theorem cell23_8173058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_8173058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173058 prefixEnd_8173058 := by exact prefixLift 8173058
  have htrace : WordTrace (prefixWord ++ tailWord_8173058) baseStart_8173058 baseEnd_8173058 := by
    simpa [prefixWord, tailWord_8173058, baseEnd_8173058] using wordTrace_append hprefix tailTrace_8173058
  have hstable : (prefixWord ++ tailWord_8173058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173058).length < 2 ^ (prefixWord ++ tailWord_8173058).sum := by decide
  have hdescent : baseEnd_8173058 < baseStart_8173058 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173090 : List Nat := [3, 3, 1, 1, 1, 1, 2, 2, 1, 8]
def baseStart_8173090 : Nat := 118140960795 + 8173090 * 2 ^ 59
def prefixEnd_8173090 : Nat := 4983230072969 + 3 ^ 40 * 8173090 * 2
def baseEnd_8173090 : Nat := 1398907867485177660495883

theorem tailTrace_8173090 : CollatzResearch.WordTrace tailWord_8173090 prefixEnd_8173090 1398907867485177660495883 := by
  unfold tailWord_8173090
  simp only [CollatzResearch.WordTrace]
  refine ⟨74524270490074564371901181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198731387973532171658403149 74524270490074564371901181)
  ·
    refine ⟨27946601433777961639462943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74524270490074564371901181 27946601433777961639462943)
    ·
      refine ⟨41919902150666942459194415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27946601433777961639462943 41919902150666942459194415)
      ·
        refine ⟨62879853226000413688791623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41919902150666942459194415 62879853226000413688791623)
        ·
          refine ⟨94319779839000620533187435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62879853226000413688791623 94319779839000620533187435)
          ·
            refine ⟨141479669758500930799781153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94319779839000620533187435 141479669758500930799781153)
            ·
              refine ⟨106109752318875698099835865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141479669758500930799781153 106109752318875698099835865)
              ·
                refine ⟨79582314239156773574876899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106109752318875698099835865 79582314239156773574876899)
                ·
                  refine ⟨119373471358735160362315349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79582314239156773574876899 119373471358735160362315349)
                  ·
                    refine ⟨1398907867485177660495883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119373471358735160362315349 1398907867485177660495883)
                    ·
                      rfl

theorem cell23_8173090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_8173090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173090 prefixEnd_8173090 := by exact prefixLift 8173090
  have htrace : WordTrace (prefixWord ++ tailWord_8173090) baseStart_8173090 baseEnd_8173090 := by
    simpa [prefixWord, tailWord_8173090, baseEnd_8173090] using wordTrace_append hprefix tailTrace_8173090
  have hstable : (prefixWord ++ tailWord_8173090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173090).length < 2 ^ (prefixWord ++ tailWord_8173090).sum := by decide
  have hdescent : baseEnd_8173090 < baseStart_8173090 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173100 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 3]
def baseStart_8173100 : Nat := 118140960795 + 8173100 * 2 ^ 59
def prefixEnd_8173100 : Nat := 4983230072969 + 3 ^ 40 * 8173100 * 2
def baseEnd_8173100 : Nat := 4196728737262077942362603

theorem tailTrace_8173100 : CollatzResearch.WordTrace tailWord_8173100 prefixEnd_8173100 4196728737262077942362603 := by
  unfold tailWord_8173100
  simp only [CollatzResearch.WordTrace]
  refine ⟨149048723345131014597734377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198731631126841352796979169 149048723345131014597734377)
  ·
    refine ⟨111786542508848260948300783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149048723345131014597734377 111786542508848260948300783)
    ·
      refine ⟨167679813763272391422451175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111786542508848260948300783 167679813763272391422451175)
      ·
        refine ⟨251519720644908587133676763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167679813763272391422451175 251519720644908587133676763)
        ·
          refine ⟨377279580967362880700515145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251519720644908587133676763 377279580967362880700515145)
          ·
            refine ⟨282959685725522160525386359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377279580967362880700515145 282959685725522160525386359)
            ·
              refine ⟨424439528588283240788079539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282959685725522160525386359 424439528588283240788079539)
              ·
                refine ⟨636659292882424861182119309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 424439528588283240788079539 636659292882424861182119309)
                ·
                  refine ⟨238747234830909322943294741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 636659292882424861182119309 238747234830909322943294741)
                  ·
                    refine ⟨11191276632698874512966941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 238747234830909322943294741 11191276632698874512966941)
                    ·
                      refine ⟨4196728737262077942362603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11191276632698874512966941 4196728737262077942362603)
                      ·
                        rfl

theorem cell23_8173100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 3].length) (baseStart_8173100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173100 prefixEnd_8173100 := by exact prefixLift 8173100
  have htrace : WordTrace (prefixWord ++ tailWord_8173100) baseStart_8173100 baseEnd_8173100 := by
    simpa [prefixWord, tailWord_8173100, baseEnd_8173100] using wordTrace_append hprefix tailTrace_8173100
  have hstable : (prefixWord ++ tailWord_8173100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173100).length < 2 ^ (prefixWord ++ tailWord_8173100).sum := by decide
  have hdescent : baseEnd_8173100 < baseStart_8173100 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173114 : List Nat := [3, 1, 1, 1, 3, 2, 1, 3, 4, 2, 2]
def baseStart_8173114 : Nat := 118140960795 + 8173114 * 2 ^ 59
def prefixEnd_8173114 : Nat := 4983230072969 + 3 ^ 40 * 8173114 * 2
def baseEnd_8173114 : Nat := 4196735925991240887587539

theorem tailTrace_8173114 : CollatzResearch.WordTrace tailWord_8173114 prefixEnd_8173114 4196735925991240887587539 := by
  unfold tailWord_8173114
  simp only [CollatzResearch.WordTrace]
  refine ⟨74524489328052827396619599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198731971541474206390985597 74524489328052827396619599)
  ·
    refine ⟨111786733992079241094929399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74524489328052827396619599 111786733992079241094929399)
    ·
      refine ⟨167680100988118861642394099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111786733992079241094929399 167680100988118861642394099)
      ·
        refine ⟨251520151482178292463591149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167680100988118861642394099 251520151482178292463591149)
        ·
          refine ⟨94320056805816859673846681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251520151482178292463591149 94320056805816859673846681)
          ·
            refine ⟨70740042604362644755385011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94320056805816859673846681 70740042604362644755385011)
            ·
              refine ⟨106110063906543967133077517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70740042604362644755385011 106110063906543967133077517)
              ·
                refine ⟨39791273964953987674904069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106110063906543967133077517 39791273964953987674904069)
                ·
                  refine ⟨7460863868428872689044513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39791273964953987674904069 7460863868428872689044513)
                  ·
                    refine ⟨5595647901321654516783385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7460863868428872689044513 5595647901321654516783385)
                    ·
                      refine ⟨4196735925991240887587539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5595647901321654516783385 4196735925991240887587539)
                      ·
                        rfl

theorem cell23_8173114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 4, 2, 2].length) (baseStart_8173114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173114 prefixEnd_8173114 := by exact prefixLift 8173114
  have htrace : WordTrace (prefixWord ++ tailWord_8173114) baseStart_8173114 baseEnd_8173114 := by
    simpa [prefixWord, tailWord_8173114, baseEnd_8173114] using wordTrace_append hprefix tailTrace_8173114
  have hstable : (prefixWord ++ tailWord_8173114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173114).length < 2 ^ (prefixWord ++ tailWord_8173114).sum := by decide
  have hdescent : baseEnd_8173114 < baseStart_8173114 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173180 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 2, 8]
def baseStart_8173180 : Nat := 118140960795 + 8173180 * 2 ^ 59
def prefixEnd_8173180 : Nat := 4983230072969 + 3 ^ 40 * 8173180 * 2
def baseEnd_8173180 : Nat := 1398923271904812543120745

theorem tailTrace_8173180 : CollatzResearch.WordTrace tailWord_8173180 prefixEnd_8173180 1398923271904812543120745 := by
  unfold tailWord_8173180
  simp only [CollatzResearch.WordTrace]
  refine ⟨149050182264986101429190497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198733576353314801905587329 149050182264986101429190497)
  ·
    refine ⟨111787636698739576071892873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149050182264986101429190497 111787636698739576071892873)
    ·
      refine ⟨83840727524054682053919655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111787636698739576071892873 83840727524054682053919655)
      ·
        refine ⟨125761091286082023080879483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83840727524054682053919655 125761091286082023080879483)
        ·
          refine ⟨188641636929123034621319225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125761091286082023080879483 188641636929123034621319225)
          ·
            refine ⟨141481227696842275965989419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188641636929123034621319225 141481227696842275965989419)
            ·
              refine ⟨212221841545263413948984129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141481227696842275965989419 212221841545263413948984129)
              ·
                refine ⟨159166381158947560461738097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212221841545263413948984129 159166381158947560461738097)
                ·
                  refine ⟨119374785869210670346303573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159166381158947560461738097 119374785869210670346303573)
                  ·
                    refine ⟨1398923271904812543120745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119374785869210670346303573 1398923271904812543120745)
                    ·
                      rfl

theorem cell23_8173180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_8173180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173180 prefixEnd_8173180 := by exact prefixLift 8173180
  have htrace : WordTrace (prefixWord ++ tailWord_8173180) baseStart_8173180 baseEnd_8173180 := by
    simpa [prefixWord, tailWord_8173180, baseEnd_8173180] using wordTrace_append hprefix tailTrace_8173180
  have hstable : (prefixWord ++ tailWord_8173180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173180).length < 2 ^ (prefixWord ++ tailWord_8173180).sum := by decide
  have hdescent : baseEnd_8173180 < baseStart_8173180 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173200 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 6]
def baseStart_8173200 : Nat := 118140960795 + 8173200 * 2 ^ 59
def prefixEnd_8173200 : Nat := 4983230072969 + 3 ^ 40 * 8173200 * 2
def baseEnd_8173200 : Nat := 4196780085327527551112143

theorem tailTrace_8173200 : CollatzResearch.WordTrace tailWord_8173200 prefixEnd_8173200 4196780085327527551112143 := by
  unfold tailWord_8173200
  simp only [CollatzResearch.WordTrace]
  refine ⟨149050546994949873137054527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198734062659933164182739369 149050546994949873137054527)
  ·
    refine ⟨223575820492424809705581791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149050546994949873137054527 223575820492424809705581791)
    ·
      refine ⟨335363730738637214558372687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223575820492424809705581791 335363730738637214558372687)
      ·
        refine ⟨503045596107955821837559031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335363730738637214558372687 503045596107955821837559031)
        ·
          refine ⟨754568394161933732756338547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503045596107955821837559031 754568394161933732756338547)
          ·
            refine ⟨1131852591242900599134507821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754568394161933732756338547 1131852591242900599134507821)
            ·
              refine ⟨424444721716087724675440433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1131852591242900599134507821 424444721716087724675440433)
              ·
                refine ⟨318333541287065793506580325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 424444721716087724675440433 318333541287065793506580325)
                ·
                  refine ⟨59687538991324836282483811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 318333541287065793506580325 59687538991324836282483811)
                  ·
                    refine ⟨89531308486987254423725717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59687538991324836282483811 89531308486987254423725717)
                    ·
                      refine ⟨4196780085327527551112143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89531308486987254423725717 4196780085327527551112143)
                      ·
                        rfl

theorem cell23_8173200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 6].length) (baseStart_8173200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173200 prefixEnd_8173200 := by exact prefixLift 8173200
  have htrace : WordTrace (prefixWord ++ tailWord_8173200) baseStart_8173200 baseEnd_8173200 := by
    simpa [prefixWord, tailWord_8173200, baseEnd_8173200] using wordTrace_append hprefix tailTrace_8173200
  have hstable : (prefixWord ++ tailWord_8173200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173200).length < 2 ^ (prefixWord ++ tailWord_8173200).sum := by decide
  have hdescent : baseEnd_8173200 < baseStart_8173200 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173217 : List Nat := [1, 2, 3, 3, 2, 1, 1, 1, 2, 1, 6]
def baseStart_8173217 : Nat := 118140960795 + 8173217 * 2 ^ 59
def prefixEnd_8173217 : Nat := 4983230072969 + 3 ^ 40 * 8173217 * 2
def baseEnd_8173217 : Nat := 4196788814498653984599565

theorem tailTrace_8173217 : CollatzResearch.WordTrace tailWord_8173217 prefixEnd_8173217 4196788814498653984599565 := by
  unfold tailWord_8173217
  simp only [CollatzResearch.WordTrace]
  refine ⟨298101714030838158177477905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198734476020558772118318603 298101714030838158177477905)
  ·
    refine ⟨223576285523128618633108429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298101714030838158177477905 223576285523128618633108429)
    ·
      refine ⟨83841107071173231987415661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223576285523128618633108429 83841107071173231987415661)
      ·
        refine ⟨31440415151689961995280873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83841107071173231987415661 31440415151689961995280873)
        ·
          refine ⟨23580311363767471496460655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31440415151689961995280873 23580311363767471496460655)
          ·
            refine ⟨35370467045651207244690983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23580311363767471496460655 35370467045651207244690983)
            ·
              refine ⟨53055700568476810867036475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35370467045651207244690983 53055700568476810867036475)
              ·
                refine ⟨79583550852715216300554713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53055700568476810867036475 79583550852715216300554713)
                ·
                  refine ⟨59687663139536412225416035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79583550852715216300554713 59687663139536412225416035)
                  ·
                    refine ⟨89531494709304618338124053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59687663139536412225416035 89531494709304618338124053)
                    ·
                      refine ⟨4196788814498653984599565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89531494709304618338124053 4196788814498653984599565)
                      ·
                        rfl

theorem cell23_8173217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_8173217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173217 prefixEnd_8173217 := by exact prefixLift 8173217
  have htrace : WordTrace (prefixWord ++ tailWord_8173217) baseStart_8173217 baseEnd_8173217 := by
    simpa [prefixWord, tailWord_8173217, baseEnd_8173217] using wordTrace_append hprefix tailTrace_8173217
  have hstable : (prefixWord ++ tailWord_8173217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173217).length < 2 ^ (prefixWord ++ tailWord_8173217).sum := by decide
  have hdescent : baseEnd_8173217 < baseStart_8173217 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173238 : List Nat := [5, 1, 3, 1, 1, 1, 2, 1, 2, 4, 2]
def baseStart_8173238 : Nat := 118140960795 + 8173238 * 2 ^ 59
def prefixEnd_8173238 : Nat := 4983230072969 + 3 ^ 40 * 8173238 * 2
def baseEnd_8173238 : Nat := 4196799597592398402436969

theorem tailTrace_8173238 : CollatzResearch.WordTrace tailWord_8173238 prefixEnd_8173238 4196799597592398402436969 := by
  unfold tailWord_8173238
  simp only [CollatzResearch.WordTrace]
  refine ⟨18631404997735129922749523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198734986642508052509328245 18631404997735129922749523)
  ·
    refine ⟨27947107496602694884124285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18631404997735129922749523 27947107496602694884124285)
    ·
      refine ⟨10480165311226010581546607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27947107496602694884124285 10480165311226010581546607)
      ·
        refine ⟨15720247966839015872319911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10480165311226010581546607 15720247966839015872319911)
        ·
          refine ⟨23580371950258523808479867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15720247966839015872319911 23580371950258523808479867)
          ·
            refine ⟨35370557925387785712719801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23580371950258523808479867 35370557925387785712719801)
            ·
              refine ⟨26527918444040839284539851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35370557925387785712719801 26527918444040839284539851)
              ·
                refine ⟨39791877666061258926809777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26527918444040839284539851 39791877666061258926809777)
                ·
                  refine ⟨29843908249545944195107333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39791877666061258926809777 29843908249545944195107333)
                  ·
                    refine ⟨5595732796789864536582625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29843908249545944195107333 5595732796789864536582625)
                    ·
                      refine ⟨4196799597592398402436969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5595732796789864536582625 4196799597592398402436969)
                      ·
                        rfl

theorem cell23_8173238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_8173238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173238 prefixEnd_8173238 := by exact prefixLift 8173238
  have htrace : WordTrace (prefixWord ++ tailWord_8173238) baseStart_8173238 baseEnd_8173238 := by
    simpa [prefixWord, tailWord_8173238, baseEnd_8173238] using wordTrace_append hprefix tailTrace_8173238
  have hstable : (prefixWord ++ tailWord_8173238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173238).length < 2 ^ (prefixWord ++ tailWord_8173238).sum := by decide
  have hdescent : baseEnd_8173238 < baseStart_8173238 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173274 : List Nat := [3, 1, 1, 2, 2, 3, 2, 3, 1, 5]
def baseStart_8173274 : Nat := 118140960795 + 8173274 * 2 ^ 59
def prefixEnd_8173274 : Nat := 4983230072969 + 3 ^ 40 * 8173274 * 2
def baseEnd_8173274 : Nat := 1398939360965320087195601

theorem tailTrace_8173274 : CollatzResearch.WordTrace tailWord_8173274 prefixEnd_8173274 1398939360965320087195601 := by
  unfold tailWord_8173274
  simp only [CollatzResearch.WordTrace]
  refine ⟨74525948247907914228075719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198735861994421104608201917 74525948247907914228075719)
  ·
    refine ⟨111788922371861871342113579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74525948247907914228075719 111788922371861871342113579)
    ·
      refine ⟨167683383557792807013170369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111788922371861871342113579 167683383557792807013170369)
      ·
        refine ⟨125762537668344605259877777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167683383557792807013170369 125762537668344605259877777)
        ·
          refine ⟨94321903251258453944908333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125762537668344605259877777 94321903251258453944908333)
          ·
            refine ⟨35370713719221920229340625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94321903251258453944908333 35370713719221920229340625)
            ·
              refine ⟨26528035289416440172005469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35370713719221920229340625 26528035289416440172005469)
              ·
                refine ⟨9948013233531165064502051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26528035289416440172005469 9948013233531165064502051)
                ·
                  refine ⟨14922019850296747596753077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9948013233531165064502051 14922019850296747596753077)
                  ·
                    refine ⟨1398939360965320087195601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14922019850296747596753077 1398939360965320087195601)
                    ·
                      rfl

theorem cell23_8173274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3, 1, 5].length) (baseStart_8173274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173274 prefixEnd_8173274 := by exact prefixLift 8173274
  have htrace : WordTrace (prefixWord ++ tailWord_8173274) baseStart_8173274 baseEnd_8173274 := by
    simpa [prefixWord, tailWord_8173274, baseEnd_8173274] using wordTrace_append hprefix tailTrace_8173274
  have hstable : (prefixWord ++ tailWord_8173274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173274).length < 2 ^ (prefixWord ++ tailWord_8173274).sum := by decide
  have hdescent : baseEnd_8173274 < baseStart_8173274 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173288 : List Nat := [2, 1, 4, 1, 3, 3, 1, 1, 3, 1, 3]
def baseStart_8173288 : Nat := 118140960795 + 8173288 * 2 ^ 59
def prefixEnd_8173288 : Nat := 4983230072969 + 3 ^ 40 * 8173288 * 2
def baseEnd_8173288 : Nat := 4196825271625123206811739

theorem tailTrace_8173288 : CollatzResearch.WordTrace tailWord_8173288 prefixEnd_8173288 4196825271625123206811739 := by
  unfold tailWord_8173288
  simp only [CollatzResearch.WordTrace]
  refine ⟨149052151806790468651656259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198736202409053958202208345 149052151806790468651656259)
  ·
    refine ⟨223578227710185702977484389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149052151806790468651656259 223578227710185702977484389)
    ·
      refine ⟨41920917695659819308278323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223578227710185702977484389 41920917695659819308278323)
      ·
        refine ⟨62881376543489728962417485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41920917695659819308278323 62881376543489728962417485)
        ·
          refine ⟨23580516203808648360906557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62881376543489728962417485 23580516203808648360906557)
          ·
            refine ⟨8842693576428243135339959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23580516203808648360906557 8842693576428243135339959)
            ·
              refine ⟨13264040364642364703009939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8842693576428243135339959 13264040364642364703009939)
              ·
                refine ⟨19896060546963547054514909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13264040364642364703009939 19896060546963547054514909)
                ·
                  refine ⟨7461022705111330145443091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19896060546963547054514909 7461022705111330145443091)
                  ·
                    refine ⟨11191534057666995218164637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7461022705111330145443091 11191534057666995218164637)
                    ·
                      refine ⟨4196825271625123206811739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11191534057666995218164637 4196825271625123206811739)
                      ·
                        rfl

theorem cell23_8173288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_8173288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173288 prefixEnd_8173288 := by exact prefixLift 8173288
  have htrace : WordTrace (prefixWord ++ tailWord_8173288) baseStart_8173288 baseEnd_8173288 := by
    simpa [prefixWord, tailWord_8173288, baseEnd_8173288] using wordTrace_append hprefix tailTrace_8173288
  have hstable : (prefixWord ++ tailWord_8173288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173288).length < 2 ^ (prefixWord ++ tailWord_8173288).sum := by decide
  have hdescent : baseEnd_8173288 < baseStart_8173288 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173294 : List Nat := [4, 1, 2, 1, 1, 2, 2, 2, 3, 1, 4]
def baseStart_8173294 : Nat := 118140960795 + 8173294 * 2 ^ 59
def prefixEnd_8173294 : Nat := 4983230072969 + 3 ^ 40 * 8173294 * 2
def baseEnd_8173294 : Nat := 4196828352509050183336711

theorem tailTrace_8173294 : CollatzResearch.WordTrace tailWord_8173294 prefixEnd_8173294 4196828352509050183336711 := by
  unfold tailWord_8173294
  simp only [CollatzResearch.WordTrace]
  refine ⟨37263065306444900041003867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198736348301039466885353957 37263065306444900041003867)
  ·
    refine ⟨55894597959667350061505801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37263065306444900041003867 55894597959667350061505801)
    ·
      refine ⟨41920948469750512546129351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55894597959667350061505801 41920948469750512546129351)
      ·
        refine ⟨62881422704625768819194027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41920948469750512546129351 62881422704625768819194027)
        ·
          refine ⟨94322134056938653228791041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62881422704625768819194027 94322134056938653228791041)
          ·
            refine ⟨70741600542703989921593281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94322134056938653228791041 70741600542703989921593281)
            ·
              refine ⟨53056200407027992441194961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70741600542703989921593281 53056200407027992441194961)
              ·
                refine ⟨39792150305270994330896221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53056200407027992441194961 39792150305270994330896221)
                ·
                  refine ⟨14922056364476622874086083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39792150305270994330896221 14922056364476622874086083)
                  ·
                    refine ⟨22383084546714934311129125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14922056364476622874086083 22383084546714934311129125)
                    ·
                      refine ⟨4196828352509050183336711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22383084546714934311129125 4196828352509050183336711)
                      ·
                        rfl

theorem cell23_8173294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_8173294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173294 prefixEnd_8173294 := by exact prefixLift 8173294
  have htrace : WordTrace (prefixWord ++ tailWord_8173294) baseStart_8173294 baseEnd_8173294 := by
    simpa [prefixWord, tailWord_8173294, baseEnd_8173294] using wordTrace_append hprefix tailTrace_8173294
  have hstable : (prefixWord ++ tailWord_8173294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173294).length < 2 ^ (prefixWord ++ tailWord_8173294).sum := by decide
  have hdescent : baseEnd_8173294 < baseStart_8173294 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173311 : List Nat := [1, 1, 2, 2, 1, 3, 2, 4, 3, 2, 2]
def baseStart_8173311 : Nat := 118140960795 + 8173311 * 2 ^ 59
def prefixEnd_8173311 : Nat := 4983230072969 + 3 ^ 40 * 8173311 * 2
def baseEnd_8173311 : Nat := 4196837081680176616824133

theorem tailTrace_8173311 : CollatzResearch.WordTrace tailWord_8173311 prefixEnd_8173311 4196837081680176616824133 := by
  unfold tailWord_8173311
  simp only [CollatzResearch.WordTrace]
  refine ⟨298105142492497612231399787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198736761661665074820933191 298105142492497612231399787)
  ·
    refine ⟨447157713738746418347099681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298105142492497612231399787 447157713738746418347099681)
    ·
      refine ⟨335368285304059813760324761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447157713738746418347099681 335368285304059813760324761)
      ·
        refine ⟨251526213978044860320243571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335368285304059813760324761 251526213978044860320243571)
        ·
          refine ⟨377289320967067290480365357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251526213978044860320243571 377289320967067290480365357)
          ·
            refine ⟨141483495362650233930137009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 377289320967067290480365357 141483495362650233930137009)
            ·
              refine ⟨106112621521987675447602757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141483495362650233930137009 106112621521987675447602757)
              ·
                refine ⟨19896116535372689146425517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106112621521987675447602757 19896116535372689146425517)
                ·
                  refine ⟨7461043700764758429909569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19896116535372689146425517 7461043700764758429909569)
                  ·
                    refine ⟨5595782775573568822432177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7461043700764758429909569 5595782775573568822432177)
                    ·
                      refine ⟨4196837081680176616824133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5595782775573568822432177 4196837081680176616824133)
                      ·
                        rfl

theorem cell23_8173311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 3, 2, 2].length) (baseStart_8173311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173311 prefixEnd_8173311 := by exact prefixLift 8173311
  have htrace : WordTrace (prefixWord ++ tailWord_8173311) baseStart_8173311 baseEnd_8173311 := by
    simpa [prefixWord, tailWord_8173311, baseEnd_8173311] using wordTrace_append hprefix tailTrace_8173311
  have hstable : (prefixWord ++ tailWord_8173311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173311).length < 2 ^ (prefixWord ++ tailWord_8173311).sum := by decide
  have hdescent : baseEnd_8173311 < baseStart_8173311 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173344 : List Nat := [2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 3]
def baseStart_8173344 : Nat := 118140960795 + 8173344 * 2 ^ 59
def prefixEnd_8173344 : Nat := 4983230072969 + 3 ^ 40 * 8173344 * 2
def baseEnd_8173344 : Nat := 4196854026541774987711481

theorem tailTrace_8173344 : CollatzResearch.WordTrace tailWord_8173344 prefixEnd_8173344 4196854026541774987711481 := by
  unfold tailWord_8173344
  simp only [CollatzResearch.WordTrace]
  refine ⟨149053173050689029433675543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198737564067585372578234057 149053173050689029433675543)
  ·
    refine ⟨223579759576033544150513315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149053173050689029433675543 223579759576033544150513315)
    ·
      refine ⟨335369639364050316225769973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223579759576033544150513315 335369639364050316225769973)
      ·
        refine ⟨31440903690379717146165935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 335369639364050316225769973 31440903690379717146165935)
        ·
          refine ⟨47161355535569575719248903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31440903690379717146165935 47161355535569575719248903)
          ·
            refine ⟨70742033303354363578873355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47161355535569575719248903 70742033303354363578873355)
            ·
              refine ⟨106113049955031545368310033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70742033303354363578873355 106113049955031545368310033)
              ·
                refine ⟨79584787466273659026232525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106113049955031545368310033 79584787466273659026232525)
                ·
                  refine ⟨29844295299852622134837197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79584787466273659026232525 29844295299852622134837197)
                  ·
                    refine ⟨11191610737444733300563949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29844295299852622134837197 11191610737444733300563949)
                    ·
                      refine ⟨4196854026541774987711481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11191610737444733300563949 4196854026541774987711481)
                      ·
                        rfl

theorem cell23_8173344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_8173344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173344 prefixEnd_8173344 := by exact prefixLift 8173344
  have htrace : WordTrace (prefixWord ++ tailWord_8173344) baseStart_8173344 baseEnd_8173344 := by
    simpa [prefixWord, tailWord_8173344, baseEnd_8173344] using wordTrace_append hprefix tailTrace_8173344
  have hstable : (prefixWord ++ tailWord_8173344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173344).length < 2 ^ (prefixWord ++ tailWord_8173344).sum := by decide
  have hdescent : baseEnd_8173344 < baseStart_8173344 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173345 : List Nat := [1, 2, 3, 2, 1, 4, 1, 4, 1, 2, 2]
def baseStart_8173345 : Nat := 118140960795 + 8173345 * 2 ^ 59
def prefixEnd_8173345 : Nat := 4983230072969 + 3 ^ 40 * 8173345 * 2
def baseEnd_8173345 : Nat := 4196854540022429483798977

theorem tailTrace_8173345 : CollatzResearch.WordTrace tailWord_8173345 prefixEnd_8173345 4196854540022429483798977 := by
  unfold tailWord_8173345
  simp only [CollatzResearch.WordTrace]
  refine ⟨298106382574374436038137489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198737588382916290692091659 298106382574374436038137489)
  ·
    refine ⟨223579786930780827028603117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298106382574374436038137489 223579786930780827028603117)
    ·
      refine ⟨83842420099042810135726169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223579786930780827028603117 83842420099042810135726169)
      ·
        refine ⟨62881815074282107601794627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83842420099042810135726169 62881815074282107601794627)
        ·
          refine ⟨94322722611423161402691941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62881815074282107601794627 94322722611423161402691941)
          ·
            refine ⟨17685510489641842763004739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94322722611423161402691941 17685510489641842763004739)
            ·
              refine ⟨26528265734462764144507109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17685510489641842763004739 26528265734462764144507109)
              ·
                refine ⟨4974049825211768277095083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26528265734462764144507109 4974049825211768277095083)
                ·
                  refine ⟨7461074737817652415642625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4974049825211768277095083 7461074737817652415642625)
                  ·
                    refine ⟨5595806053363239311731969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7461074737817652415642625 5595806053363239311731969)
                    ·
                      refine ⟨4196854540022429483798977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5595806053363239311731969 4196854540022429483798977)
                      ·
                        rfl

theorem cell23_8173345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 4, 1, 2, 2].length) (baseStart_8173345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173345 prefixEnd_8173345 := by exact prefixLift 8173345
  have htrace : WordTrace (prefixWord ++ tailWord_8173345) baseStart_8173345 baseEnd_8173345 := by
    simpa [prefixWord, tailWord_8173345, baseEnd_8173345] using wordTrace_append hprefix tailTrace_8173345
  have hstable : (prefixWord ++ tailWord_8173345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173345).length < 2 ^ (prefixWord ++ tailWord_8173345).sum := by decide
  have hdescent : baseEnd_8173345 < baseStart_8173345 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173347 : List Nat := [1, 1, 1, 4, 2, 1, 3, 1, 2, 7]
def baseStart_8173347 : Nat := 118140960795 + 8173347 * 2 ^ 59
def prefixEnd_8173347 : Nat := 4983230072969 + 3 ^ 40 * 8173347 * 2
def baseEnd_8173347 : Nat := 1398951855661246158657989

theorem tailTrace_8173347 : CollatzResearch.WordTrace tailWord_8173347 prefixEnd_8173347 1398951855661246158657989 := by
  unfold tailWord_8173347
  simp only [CollatzResearch.WordTrace]
  refine ⟨298106455520367190379710295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198737637013578126919806863 298106455520367190379710295)
  ·
    refine ⟨447159683280550785569565443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298106455520367190379710295 447159683280550785569565443)
    ·
      refine ⟨670739524920826178354348165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447159683280550785569565443 670739524920826178354348165)
      ·
        refine ⟨125763660922654908441440281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 670739524920826178354348165 125763660922654908441440281)
        ·
          refine ⟨94322745691991181331080211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125763660922654908441440281 94322745691991181331080211)
          ·
            refine ⟨141484118537986771996620317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94322745691991181331080211 141484118537986771996620317)
            ·
              refine ⟨53056544451745039498732619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141484118537986771996620317 53056544451745039498732619)
              ·
                refine ⟨79584816677617559248098929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53056544451745039498732619 79584816677617559248098929)
                ·
                  refine ⟨59688612508213169436074197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79584816677617559248098929 59688612508213169436074197)
                  ·
                    refine ⟨1398951855661246158657989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59688612508213169436074197 1398951855661246158657989)
                    ·
                      rfl

theorem cell23_8173347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 7].length) (baseStart_8173347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173347 prefixEnd_8173347 := by exact prefixLift 8173347
  have htrace : WordTrace (prefixWord ++ tailWord_8173347) baseStart_8173347 baseEnd_8173347 := by
    simpa [prefixWord, tailWord_8173347, baseEnd_8173347] using wordTrace_append hprefix tailTrace_8173347
  have hstable : (prefixWord ++ tailWord_8173347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173347).length < 2 ^ (prefixWord ++ tailWord_8173347).sum := by decide
  have hdescent : baseEnd_8173347 < baseStart_8173347 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173358 : List Nat := [4, 1, 3, 2, 2, 1, 2, 1, 1, 2, 4]
def baseStart_8173358 : Nat := 118140960795 + 8173358 * 2 ^ 59
def prefixEnd_8173358 : Nat := 4983230072969 + 3 ^ 40 * 8173358 * 2
def baseEnd_8173358 : Nat := 4196861215270937932936417

theorem tailTrace_8173358 : CollatzResearch.WordTrace tailWord_8173358 prefixEnd_8173358 4196861215270937932936417 := by
  unfold tailWord_8173358
  simp only [CollatzResearch.WordTrace]
  refine ⟨37263357090415917407295091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198737904482218226172240485 37263357090415917407295091)
  ·
    refine ⟨55895035635623876110942637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37263357090415917407295091 55895035635623876110942637)
    ·
      refine ⟨20960638363358953541603489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55895035635623876110942637 20960638363358953541603489)
      ·
        refine ⟨15720478772519215156202617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20960638363358953541603489 15720478772519215156202617)
        ·
          refine ⟨11790359079389411367151963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15720478772519215156202617 11790359079389411367151963)
          ·
            refine ⟨17685538619084117050727945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11790359079389411367151963 17685538619084117050727945)
            ·
              refine ⟨13264153964313087788045959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17685538619084117050727945 13264153964313087788045959)
              ·
                refine ⟨19896230946469631682068939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13264153964313087788045959 19896230946469631682068939)
                ·
                  refine ⟨29844346419704447523103409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19896230946469631682068939 29844346419704447523103409)
                  ·
                    refine ⟨22383259814778335642327557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29844346419704447523103409 22383259814778335642327557)
                    ·
                      refine ⟨4196861215270937932936417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22383259814778335642327557 4196861215270937932936417)
                      ·
                        rfl

theorem cell23_8173358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_8173358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173358 prefixEnd_8173358 := by exact prefixLift 8173358
  have htrace : WordTrace (prefixWord ++ tailWord_8173358) baseStart_8173358 baseEnd_8173358 := by
    simpa [prefixWord, tailWord_8173358, baseEnd_8173358] using wordTrace_append hprefix tailTrace_8173358
  have hstable : (prefixWord ++ tailWord_8173358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173358).length < 2 ^ (prefixWord ++ tailWord_8173358).sum := by decide
  have hdescent : baseEnd_8173358 < baseStart_8173358 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173361 : List Nat := [1, 2, 2, 3, 2, 3, 2, 1, 1, 3, 3]
def baseStart_8173361 : Nat := 118140960795 + 8173361 * 2 ^ 59
def prefixEnd_8173361 : Nat := 4983230072969 + 3 ^ 40 * 8173361 * 2
def baseEnd_8173361 : Nat := 4196862755712901421198903

theorem tailTrace_8173361 : CollatzResearch.WordTrace tailWord_8173361 prefixEnd_8173361 4196862755712901421198903 := by
  unfold tailWord_8173361
  simp only [CollatzResearch.WordTrace]
  refine ⟨298106966142316470770719937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198737977428210980513813291 298106966142316470770719937)
  ·
    refine ⟨223580224606737353078039953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298106966142316470770719937 223580224606737353078039953)
    ·
      refine ⟨167685168455053014808529965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223580224606737353078039953 167685168455053014808529965)
      ·
        refine ⟨62881938170644880553198737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167685168455053014808529965 62881938170644880553198737)
        ·
          refine ⟨47161453627983660414899053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62881938170644880553198737 47161453627983660414899053)
          ·
            refine ⟨17685545110493872655587145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47161453627983660414899053 17685545110493872655587145)
            ·
              refine ⟨13264158832870404491690359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17685545110493872655587145 13264158832870404491690359)
              ·
                refine ⟨19896238249305606737535539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13264158832870404491690359 19896238249305606737535539)
                ·
                  refine ⟨29844357373958410106303309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19896238249305606737535539 29844357373958410106303309)
                  ·
                    refine ⟨11191634015234403789863741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29844357373958410106303309 11191634015234403789863741)
                    ·
                      refine ⟨4196862755712901421198903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11191634015234403789863741 4196862755712901421198903)
                      ·
                        rfl

theorem cell23_8173361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_8173361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173361 prefixEnd_8173361 := by exact prefixLift 8173361
  have htrace : WordTrace (prefixWord ++ tailWord_8173361) baseStart_8173361 baseEnd_8173361 := by
    simpa [prefixWord, tailWord_8173361, baseEnd_8173361] using wordTrace_append hprefix tailTrace_8173361
  have hstable : (prefixWord ++ tailWord_8173361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173361).length < 2 ^ (prefixWord ++ tailWord_8173361).sum := by decide
  have hdescent : baseEnd_8173361 < baseStart_8173361 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173382 : List Nat := [6, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3]
def baseStart_8173382 : Nat := 118140960795 + 8173382 * 2 ^ 59
def prefixEnd_8173382 : Nat := 4983230072969 + 3 ^ 40 * 8173382 * 2
def baseEnd_8173382 : Nat := 4196873538806645839036307

theorem tailTrace_8173382 : CollatzResearch.WordTrace tailWord_8173382 prefixEnd_8173382 4196873538806645839036307 := by
  unfold tailWord_8173382
  simp only [CollatzResearch.WordTrace]
  refine ⟨9315866627351262229913575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 198738488050160260904822933 9315866627351262229913575)
  ·
    refine ⟨13973799941026893344870363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9315866627351262229913575 13973799941026893344870363)
    ·
      refine ⟨20960699911540340017305545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13973799941026893344870363 20960699911540340017305545)
      ·
        refine ⟨15720524933655255012979159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20960699911540340017305545 15720524933655255012979159)
        ·
          refine ⟨23580787400482882519468739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15720524933655255012979159 23580787400482882519468739)
          ·
            refine ⟨35371181100724323779203109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23580787400482882519468739 35371181100724323779203109)
            ·
              refine ⟨6632096456385810708600583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35371181100724323779203109 6632096456385810708600583)
              ·
                refine ⟨9948144684578716062900875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6632096456385810708600583 9948144684578716062900875)
                ·
                  refine ⟨14922217026868074094351313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9948144684578716062900875 14922217026868074094351313)
                  ·
                    refine ⟨11191662770151055570763485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14922217026868074094351313 11191662770151055570763485)
                    ·
                      refine ⟨4196873538806645839036307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11191662770151055570763485 4196873538806645839036307)
                      ·
                        rfl

theorem cell23_8173382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_8173382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173382 prefixEnd_8173382 := by exact prefixLift 8173382
  have htrace : WordTrace (prefixWord ++ tailWord_8173382) baseStart_8173382 baseEnd_8173382 := by
    simpa [prefixWord, tailWord_8173382, baseEnd_8173382] using wordTrace_append hprefix tailTrace_8173382
  have hstable : (prefixWord ++ tailWord_8173382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173382).length < 2 ^ (prefixWord ++ tailWord_8173382).sum := by decide
  have hdescent : baseEnd_8173382 < baseStart_8173382 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173394 : List Nat := [3, 2, 2, 1, 1, 3, 1, 2, 2, 6]
def baseStart_8173394 : Nat := 118140960795 + 8173394 * 2 ^ 59
def prefixEnd_8173394 : Nat := 4983230072969 + 3 ^ 40 * 8173394 * 2
def baseEnd_8173394 : Nat := 1398959900191499930695417

theorem tailTrace_8173394 : CollatzResearch.WordTrace tailWord_8173394 prefixEnd_8173394 1398959900191499930695417 := by
  unfold tailWord_8173394
  simp only [CollatzResearch.WordTrace]
  refine ⟨74527042437799229351667809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198738779834131278271114157 74527042437799229351667809)
  ·
    refine ⟨55895281828349422013750857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74527042437799229351667809 55895281828349422013750857)
    ·
      refine ⟨41921461371262066510313143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55895281828349422013750857 41921461371262066510313143)
      ·
        refine ⟨62882192056893099765469715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41921461371262066510313143 62882192056893099765469715)
        ·
          refine ⟨94323288085339649648204573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62882192056893099765469715 94323288085339649648204573)
          ·
            refine ⟨35371233032002368618076715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94323288085339649648204573 35371233032002368618076715)
            ·
              refine ⟨53056849548003552927115073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35371233032002368618076715 53056849548003552927115073)
              ·
                refine ⟨39792637161002664695336305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53056849548003552927115073 39792637161002664695336305)
                ·
                  refine ⟨29844477870751998521502229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39792637161002664695336305 29844477870751998521502229)
                  ·
                    refine ⟨1398959900191499930695417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29844477870751998521502229 1398959900191499930695417)
                    ·
                      rfl

theorem cell23_8173394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_8173394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173394 prefixEnd_8173394 := by exact prefixLift 8173394
  have htrace : WordTrace (prefixWord ++ tailWord_8173394) baseStart_8173394 baseEnd_8173394 := by
    simpa [prefixWord, tailWord_8173394, baseEnd_8173394] using wordTrace_append hprefix tailTrace_8173394
  have hstable : (prefixWord ++ tailWord_8173394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173394).length < 2 ^ (prefixWord ++ tailWord_8173394).sum := by decide
  have hdescent : baseEnd_8173394 < baseStart_8173394 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173417 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 1, 1, 9]
def baseStart_8173417 : Nat := 118140960795 + 8173417 * 2 ^ 59
def prefixEnd_8173417 : Nat := 4983230072969 + 3 ^ 40 * 8173417 * 2
def baseEnd_8173417 : Nat := 4196891510629553202098645

theorem tailTrace_8173417 : CollatzResearch.WordTrace tailWord_8173417 prefixEnd_8173417 4196891510629553202098645 := by
  unfold tailWord_8173417
  simp only [CollatzResearch.WordTrace]
  refine ⟨298109008630113592334758505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198739339086742394889839003 298109008630113592334758505)
  ·
    refine ⟨223581756472585194251068879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298109008630113592334758505 223581756472585194251068879)
    ·
      refine ⟨335372634708877791376603319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223581756472585194251068879 335372634708877791376603319)
      ·
        refine ⟨503058952063316687064904979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335372634708877791376603319 503058952063316687064904979)
        ·
          refine ⟨754588428094975030597357469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503058952063316687064904979 754588428094975030597357469)
          ·
            refine ⟨282970660535615636474009051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 754588428094975030597357469 282970660535615636474009051)
            ·
              refine ⟨424455990803423454711013577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282970660535615636474009051 424455990803423454711013577)
              ·
                refine ⟨318341993102567591033260183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 424455990803423454711013577 318341993102567591033260183)
                ·
                  refine ⟨477512989653851386549890275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 318341993102567591033260183 477512989653851386549890275)
                  ·
                    refine ⟨716269484480777079824835413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 477512989653851386549890275 716269484480777079824835413)
                    ·
                      refine ⟨4196891510629553202098645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 716269484480777079824835413 4196891510629553202098645)
                      ·
                        rfl

theorem cell23_8173417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 1, 9].length) (baseStart_8173417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173417 prefixEnd_8173417 := by exact prefixLift 8173417
  have htrace : WordTrace (prefixWord ++ tailWord_8173417) baseStart_8173417 baseEnd_8173417 := by
    simpa [prefixWord, tailWord_8173417, baseEnd_8173417] using wordTrace_append hprefix tailTrace_8173417
  have hstable : (prefixWord ++ tailWord_8173417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173417).length < 2 ^ (prefixWord ++ tailWord_8173417).sum := by decide
  have hdescent : baseEnd_8173417 < baseStart_8173417 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173434 : List Nat := [3, 1, 1, 1, 1, 1, 4, 2, 1, 5, 3]
def baseStart_8173434 : Nat := 118140960795 + 8173434 * 2 ^ 59
def prefixEnd_8173434 : Nat := 4983230072969 + 3 ^ 40 * 8173434 * 2
def baseEnd_8173434 : Nat := 4196900239800679635586067

theorem tailTrace_8173434 : CollatzResearch.WordTrace tailWord_8173434 prefixEnd_8173434 4196900239800679635586067 := by
  unfold tailWord_8173434
  simp only [CollatzResearch.WordTrace]
  refine ⟨74527407167763001059531839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198739752447368002825418237 74527407167763001059531839)
  ·
    refine ⟨111791110751644501589297759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74527407167763001059531839 111791110751644501589297759)
    ·
      refine ⟨167686666127466752383946639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111791110751644501589297759 167686666127466752383946639)
      ·
        refine ⟨251529999191200128575919959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167686666127466752383946639 251529999191200128575919959)
        ·
          refine ⟨377294998786800192863879939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251529999191200128575919959 377294998786800192863879939)
          ·
            refine ⟨565942498180200289295819909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377294998786800192863879939 565942498180200289295819909)
            ·
              refine ⟨106114218408787554242966233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 565942498180200289295819909 106114218408787554242966233)
              ·
                refine ⟨79585663806590665682224675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106114218408787554242966233 79585663806590665682224675)
                ·
                  refine ⟨119378495709885998523337013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79585663806590665682224675 119378495709885998523337013)
                  ·
                    refine ⟨11191733972801812361562845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 119378495709885998523337013 11191733972801812361562845)
                    ·
                      refine ⟨4196900239800679635586067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11191733972801812361562845 4196900239800679635586067)
                      ·
                        rfl

theorem cell23_8173434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 1, 5, 3].length) (baseStart_8173434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173434 prefixEnd_8173434 := by exact prefixLift 8173434
  have htrace : WordTrace (prefixWord ++ tailWord_8173434) baseStart_8173434 baseEnd_8173434 := by
    simpa [prefixWord, tailWord_8173434, baseEnd_8173434] using wordTrace_append hprefix tailTrace_8173434
  have hstable : (prefixWord ++ tailWord_8173434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173434).length < 2 ^ (prefixWord ++ tailWord_8173434).sum := by decide
  have hdescent : baseEnd_8173434 < baseStart_8173434 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173438 : List Nat := [4, 2, 3, 1, 1, 2, 1, 1, 2, 1, 5]
def baseStart_8173438 : Nat := 118140960795 + 8173438 * 2 ^ 59
def prefixEnd_8173438 : Nat := 4983230072969 + 3 ^ 40 * 8173438 * 2
def baseEnd_8173438 : Nat := 4196902293723297619936049

theorem tailTrace_8173438 : CollatzResearch.WordTrace tailWord_8173438 prefixEnd_8173438 4196902293723297619936049 := by
  unfold tailWord_8173438
  simp only [CollatzResearch.WordTrace]
  refine ⟨37263721820379689115159121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198739849708691675280848645 37263721820379689115159121)
  ·
    refine ⟨27947791365284766836369341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37263721820379689115159121 27947791365284766836369341)
    ·
      refine ⟨10480421761981787563638503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27947791365284766836369341 10480421761981787563638503)
      ·
        refine ⟨15720632642972681345457755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10480421761981787563638503 15720632642972681345457755)
        ·
          refine ⟨23580948964459022018186633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15720632642972681345457755 23580948964459022018186633)
          ·
            refine ⟨17685711723344266513639975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23580948964459022018186633 17685711723344266513639975)
            ·
              refine ⟨26528567585016399770459963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17685711723344266513639975 26528567585016399770459963)
              ·
                refine ⟨39792851377524599655689945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26528567585016399770459963 39792851377524599655689945)
                ·
                  refine ⟨29844638533143449741767459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39792851377524599655689945 29844638533143449741767459)
                  ·
                    refine ⟨44766957799715174612651189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29844638533143449741767459 44766957799715174612651189)
                    ·
                      refine ⟨4196902293723297619936049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44766957799715174612651189 4196902293723297619936049)
                      ·
                        rfl

theorem cell23_8173438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_8173438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173438 prefixEnd_8173438 := by exact prefixLift 8173438
  have htrace : WordTrace (prefixWord ++ tailWord_8173438) baseStart_8173438 baseEnd_8173438 := by
    simpa [prefixWord, tailWord_8173438, baseEnd_8173438] using wordTrace_append hprefix tailTrace_8173438
  have hstable : (prefixWord ++ tailWord_8173438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173438).length < 2 ^ (prefixWord ++ tailWord_8173438).sum := by decide
  have hdescent : baseEnd_8173438 < baseStart_8173438 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173458 : List Nat := [3, 2, 3, 2, 1, 3, 1, 1, 7]
def baseStart_8173458 : Nat := 118140960795 + 8173458 * 2 ^ 59
def prefixEnd_8173458 : Nat := 4983230072969 + 3 ^ 40 * 8173458 * 2
def baseEnd_8173458 : Nat := 466323618148487504631773

theorem tailTrace_8173458 : CollatzResearch.WordTrace tailWord_8173458 prefixEnd_8173458 466323618148487504631773 := by
  unfold tailWord_8173458
  simp only [CollatzResearch.WordTrace]
  refine ⟨74527626005741264084250257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198740336015310037558000685 74527626005741264084250257)
  ·
    refine ⟨55895719504305948063187693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74527626005741264084250257 55895719504305948063187693)
    ·
      refine ⟨20960894814114730523695385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55895719504305948063187693 20960894814114730523695385)
      ·
        refine ⟨15720671110586047892771539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20960894814114730523695385 15720671110586047892771539)
        ·
          refine ⟨23581006665879071839157309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15720671110586047892771539 23581006665879071839157309)
          ·
            refine ⟨8842877499704651939683991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23581006665879071839157309 8842877499704651939683991)
            ·
              refine ⟨13264316249556977909525987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8842877499704651939683991 13264316249556977909525987)
              ·
                refine ⟨19896474374335466864288981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13264316249556977909525987 19896474374335466864288981)
                ·
                  refine ⟨466323618148487504631773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19896474374335466864288981 466323618148487504631773)
                  ·
                    rfl

theorem cell23_8173458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 7].length) (baseStart_8173458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173458 prefixEnd_8173458 := by exact prefixLift 8173458
  have htrace : WordTrace (prefixWord ++ tailWord_8173458) baseStart_8173458 baseEnd_8173458 := by
    simpa [prefixWord, tailWord_8173458, baseEnd_8173458] using wordTrace_append hprefix tailTrace_8173458
  have hstable : (prefixWord ++ tailWord_8173458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173458).length < 2 ^ (prefixWord ++ tailWord_8173458).sum := by decide
  have hdescent : baseEnd_8173458 < baseStart_8173458 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173461 : List Nat := [1, 3, 2, 1, 1, 3, 2, 1, 2, 5, 2]
def baseStart_8173461 : Nat := 118140960795 + 8173461 * 2 ^ 59
def prefixEnd_8173461 : Nat := 4983230072969 + 3 ^ 40 * 8173461 * 2
def baseEnd_8173461 : Nat := 4196914103778351029948443

theorem tailTrace_8173461 : CollatzResearch.WordTrace tailWord_8173461 prefixEnd_8173461 4196914103778351029948443 := by
  unfold tailWord_8173461
  simp only [CollatzResearch.WordTrace]
  refine ⟨298110613441954187849360237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198740408961302791899573491 298110613441954187849360237)
  ·
    refine ⟨111791480040732820443510089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298110613441954187849360237 111791480040732820443510089)
    ·
      refine ⟨83843610030549615332632567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111791480040732820443510089 83843610030549615332632567)
      ·
        refine ⟨125765415045824422998948851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83843610030549615332632567 125765415045824422998948851)
        ·
          refine ⟨188648122568736634498423277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125765415045824422998948851 188648122568736634498423277)
          ·
            refine ⟨70743045963276237936908729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188648122568736634498423277 70743045963276237936908729)
            ·
              refine ⟨53057284472457178452681547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70743045963276237936908729 53057284472457178452681547)
              ·
                refine ⟨79585926708685767679022321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53057284472457178452681547 79585926708685767679022321)
                ·
                  refine ⟨59689445031514325759266741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79585926708685767679022321 59689445031514325759266741)
                  ·
                    refine ⟨5595885471704468039931257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59689445031514325759266741 5595885471704468039931257)
                    ·
                      refine ⟨4196914103778351029948443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5595885471704468039931257 4196914103778351029948443)
                      ·
                        rfl

theorem cell23_8173461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 5, 2].length) (baseStart_8173461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173461 prefixEnd_8173461 := by exact prefixLift 8173461
  have htrace : WordTrace (prefixWord ++ tailWord_8173461) baseStart_8173461 baseEnd_8173461 := by
    simpa [prefixWord, tailWord_8173461, baseEnd_8173461] using wordTrace_append hprefix tailTrace_8173461
  have hstable : (prefixWord ++ tailWord_8173461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173461).length < 2 ^ (prefixWord ++ tailWord_8173461).sum := by decide
  have hdescent : baseEnd_8173461 < baseStart_8173461 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173491 : List Nat := [1, 1, 1, 2, 3, 1, 6, 1, 2, 1, 4]
def baseStart_8173491 : Nat := 118140960795 + 8173491 * 2 ^ 59
def prefixEnd_8173491 : Nat := 4983230072969 + 3 ^ 40 * 8173491 * 2
def baseEnd_8173491 : Nat := 4196929508197985912573305

theorem tailTrace_8173491 : CollatzResearch.WordTrace tailWord_8173491 prefixEnd_8173491 4196929508197985912573305 := by
  unfold tailWord_8173491
  simp only [CollatzResearch.WordTrace]
  refine ⟨298111707631845502972952327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198741138421230335315301551 298111707631845502972952327)
  ·
    refine ⟨447167561447768254459428491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298111707631845502972952327 447167561447768254459428491)
    ·
      refine ⟨670751342171652381689142737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447167561447768254459428491 670751342171652381689142737)
      ·
        refine ⟨503063506628739286266857053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 670751342171652381689142737 503063506628739286266857053)
        ·
          refine ⟨188648814985777232350071395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 503063506628739286266857053 188648814985777232350071395)
          ·
            refine ⟨282973222478665848525107093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188648814985777232350071395 282973222478665848525107093)
            ·
              refine ⟨13264369803687461649614395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 282973222478665848525107093 13264369803687461649614395)
              ·
                refine ⟨19896554705531192474421593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13264369803687461649614395 19896554705531192474421593)
                ·
                  refine ⟨14922416029148394355816195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19896554705531192474421593 14922416029148394355816195)
                  ·
                    refine ⟨22383624043722591533724293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14922416029148394355816195 22383624043722591533724293)
                    ·
                      refine ⟨4196929508197985912573305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22383624043722591533724293 4196929508197985912573305)
                      ·
                        rfl

theorem cell23_8173491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 2, 1, 4].length) (baseStart_8173491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173491 prefixEnd_8173491 := by exact prefixLift 8173491
  have htrace : WordTrace (prefixWord ++ tailWord_8173491) baseStart_8173491 baseEnd_8173491 := by
    simpa [prefixWord, tailWord_8173491, baseEnd_8173491] using wordTrace_append hprefix tailTrace_8173491
  have hstable : (prefixWord ++ tailWord_8173491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173491).length < 2 ^ (prefixWord ++ tailWord_8173491).sum := by decide
  have hdescent : baseEnd_8173491 < baseStart_8173491 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173504 : List Nat := [2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 6]
def baseStart_8173504 : Nat := 118140960795 + 8173504 * 2 ^ 59
def prefixEnd_8173504 : Nat := 4983230072969 + 3 ^ 40 * 8173504 * 2
def baseEnd_8173504 : Nat := 4196936183446494361710745

theorem tailTrace_8173504 : CollatzResearch.WordTrace tailWord_8173504 prefixEnd_8173504 4196936183446494361710745 := by
  unfold tailWord_8173504
  simp only [CollatzResearch.WordTrace]
  refine ⟨149056090890399203096587783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198741454520532270795450377 149056090890399203096587783)
  ·
    refine ⟨223584136335598804644881675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149056090890399203096587783 223584136335598804644881675)
    ·
      refine ⟨335376204503398206967322513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223584136335598804644881675 335376204503398206967322513)
      ·
        refine ⟨251532153377548655225491885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335376204503398206967322513 251532153377548655225491885)
        ·
          refine ⟨94324557516580745709559457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251532153377548655225491885 94324557516580745709559457)
          ·
            refine ⟨70743418137435559282169593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94324557516580745709559457 70743418137435559282169593)
            ·
              refine ⟨53057563603076669461627195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70743418137435559282169593 53057563603076669461627195)
              ·
                refine ⟨79586345404615004192440793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53057563603076669461627195 79586345404615004192440793)
                ·
                  refine ⟨59689759053461253144330595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79586345404615004192440793 59689759053461253144330595)
                  ·
                    refine ⟨89534638580191879716495893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59689759053461253144330595 89534638580191879716495893)
                    ·
                      refine ⟨4196936183446494361710745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89534638580191879716495893 4196936183446494361710745)
                      ·
                        rfl

theorem cell23_8173504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_8173504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173504 prefixEnd_8173504 := by exact prefixLift 8173504
  have htrace : WordTrace (prefixWord ++ tailWord_8173504) baseStart_8173504 baseEnd_8173504 := by
    simpa [prefixWord, tailWord_8173504, baseEnd_8173504] using wordTrace_append hprefix tailTrace_8173504
  have hstable : (prefixWord ++ tailWord_8173504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173504).length < 2 ^ (prefixWord ++ tailWord_8173504).sum := by decide
  have hdescent : baseEnd_8173504 < baseStart_8173504 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173514 : List Nat := [3, 1, 2, 1, 2, 1, 2, 3, 8]
def baseStart_8173514 : Nat := 118140960795 + 8173514 * 2 ^ 59
def prefixEnd_8173514 : Nat := 4983230072969 + 3 ^ 40 * 8173514 * 2
def baseEnd_8173514 : Nat := 466326813139226591398411

theorem tailTrace_8173514 : CollatzResearch.WordTrace tailWord_8173514 prefixEnd_8173514 466326813139226591398411 := by
  unfold tailWord_8173514
  simp only [CollatzResearch.WordTrace]
  refine ⟨74528136627690544475259899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198741697673841451934026397 74528136627690544475259899)
  ·
    refine ⟨111792204941535816712889849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74528136627690544475259899 111792204941535816712889849)
    ·
      refine ⟨83844153706151862534667387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111792204941535816712889849 83844153706151862534667387)
      ·
        refine ⟨125766230559227793802001081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83844153706151862534667387 125766230559227793802001081)
        ·
          refine ⟨94324672919420845351500811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125766230559227793802001081 94324672919420845351500811)
          ·
            refine ⟨141487009379131268027251217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94324672919420845351500811 141487009379131268027251217)
            ·
              refine ⟨106115257034348451020438413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141487009379131268027251217 106115257034348451020438413)
              ·
                refine ⟨39793221387880669132664405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106115257034348451020438413 39793221387880669132664405)
                ·
                  refine ⟨466326813139226591398411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39793221387880669132664405 466326813139226591398411)
                  ·
                    rfl

theorem cell23_8173514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 8].length) (baseStart_8173514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173514 prefixEnd_8173514 := by exact prefixLift 8173514
  have htrace : WordTrace (prefixWord ++ tailWord_8173514) baseStart_8173514 baseEnd_8173514 := by
    simpa [prefixWord, tailWord_8173514, baseEnd_8173514] using wordTrace_append hprefix tailTrace_8173514
  have hstable : (prefixWord ++ tailWord_8173514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173514).length < 2 ^ (prefixWord ++ tailWord_8173514).sum := by decide
  have hdescent : baseEnd_8173514 < baseStart_8173514 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173575 : List Nat := [1, 1, 4, 3, 1, 3, 2, 1, 3, 1, 3]
def baseStart_8173575 : Nat := 118140960795 + 8173575 * 2 ^ 59
def prefixEnd_8173575 : Nat := 4983230072969 + 3 ^ 40 * 8173575 * 2
def baseEnd_8173575 : Nat := 4196972640572963583922919

theorem tailTrace_8173575 : CollatzResearch.WordTrace tailWord_8173575 prefixEnd_8173575 4196972640572963583922919 := by
  unfold tailWord_8173575
  simp only [CollatzResearch.WordTrace]
  refine ⟨298114771363541185319010179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198743180909027456879340119 298114771363541185319010179)
  ·
    refine ⟨447172157045311777978515269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298114771363541185319010179 447172157045311777978515269)
    ·
      refine ⟨83844779445995958370971613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 447172157045311777978515269 83844779445995958370971613)
      ·
        refine ⟨31441792292248484389114355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83844779445995958370971613 31441792292248484389114355)
        ·
          refine ⟨47162688438372726583671533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31441792292248484389114355 47162688438372726583671533)
          ·
            refine ⟨17686008164389772468876825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47162688438372726583671533 17686008164389772468876825)
            ·
              refine ⟨13264506123292329351657619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17686008164389772468876825 13264506123292329351657619)
              ·
                refine ⟨19896759184938494027486429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13264506123292329351657619 19896759184938494027486429)
                ·
                  refine ⟨7461284694351935260307411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19896759184938494027486429 7461284694351935260307411)
                  ·
                    refine ⟨11191927041527902890461117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7461284694351935260307411 11191927041527902890461117)
                    ·
                      refine ⟨4196972640572963583922919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11191927041527902890461117 4196972640572963583922919)
                      ·
                        rfl

theorem cell23_8173575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_8173575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173575 prefixEnd_8173575 := by exact prefixLift 8173575
  have htrace : WordTrace (prefixWord ++ tailWord_8173575) baseStart_8173575 baseEnd_8173575 := by
    simpa [prefixWord, tailWord_8173575, baseEnd_8173575] using wordTrace_append hprefix tailTrace_8173575
  have hstable : (prefixWord ++ tailWord_8173575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173575).length < 2 ^ (prefixWord ++ tailWord_8173575).sum := by decide
  have hdescent : baseEnd_8173575 < baseStart_8173575 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173618 : List Nat := [3, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5]
def baseStart_8173618 : Nat := 118140960795 + 8173618 * 2 ^ 59
def prefixEnd_8173618 : Nat := 4983230072969 + 3 ^ 40 * 8173618 * 2
def baseEnd_8173618 : Nat := 4196994720241106915685221

theorem tailTrace_8173618 : CollatzResearch.WordTrace tailWord_8173618 prefixEnd_8173618 4196994720241106915685221 := by
  unfold tailWord_8173618
  simp only [CollatzResearch.WordTrace]
  refine ⟨74529084925596350915706377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198744226468256935775217005 74529084925596350915706377)
  ·
    refine ⟨55896813694197263186779783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74529084925596350915706377 55896813694197263186779783)
    ·
      refine ⟨83845220541295894780169675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55896813694197263186779783 83845220541295894780169675)
      ·
        refine ⟨125767830811943842170254513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83845220541295894780169675 125767830811943842170254513)
        ·
          refine ⟨94325873108957881627690885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125767830811943842170254513 94325873108957881627690885)
          ·
            refine ⟨17686101207929602805192041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94325873108957881627690885 17686101207929602805192041)
            ·
              refine ⟨13264575905947202103894031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17686101207929602805192041 13264575905947202103894031)
              ·
                refine ⟨19896863858920803155841047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13264575905947202103894031 19896863858920803155841047)
                ·
                  refine ⟨29845295788381204733761571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19896863858920803155841047 29845295788381204733761571)
                  ·
                    refine ⟨44767943682571807100642357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29845295788381204733761571 44767943682571807100642357)
                    ·
                      refine ⟨4196994720241106915685221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44767943682571807100642357 4196994720241106915685221)
                      ·
                        rfl

theorem cell23_8173618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5].length) (baseStart_8173618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173618 prefixEnd_8173618 := by exact prefixLift 8173618
  have htrace : WordTrace (prefixWord ++ tailWord_8173618) baseStart_8173618 baseEnd_8173618 := by
    simpa [prefixWord, tailWord_8173618, baseEnd_8173618] using wordTrace_append hprefix tailTrace_8173618
  have hstable : (prefixWord ++ tailWord_8173618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173618).length < 2 ^ (prefixWord ++ tailWord_8173618).sum := by decide
  have hdescent : baseEnd_8173618 < baseStart_8173618 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173632 : List Nat := [2, 1, 1, 2, 2, 6, 1, 1, 3, 2, 2]
def baseStart_8173632 : Nat := 118140960795 + 8173632 * 2 ^ 59
def prefixEnd_8173632 : Nat := 4983230072969 + 3 ^ 40 * 8173632 * 2
def baseEnd_8173632 : Nat := 4197001908970269860910157

theorem tailTrace_8173632 : CollatzResearch.WordTrace tailWord_8173632 prefixEnd_8173632 4197001908970269860910157 := by
  unfold tailWord_8173632
  simp only [CollatzResearch.WordTrace]
  refine ⟨149058425162167342026917575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198744566882889789369223433 149058425162167342026917575)
  ·
    refine ⟨223587637743251013040376363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149058425162167342026917575 223587637743251013040376363)
    ·
      refine ⟨335381456614876519560564545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223587637743251013040376363 335381456614876519560564545)
      ·
        refine ⟨251536092461157389670423409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335381456614876519560564545 251536092461157389670423409)
        ·
          refine ⟨188652069345868042252817557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251536092461157389670423409 188652069345868042252817557)
          ·
            refine ⟨8843065750587564480600823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 188652069345868042252817557 8843065750587564480600823)
            ·
              refine ⟨13264598625881346720901235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8843065750587564480600823 13264598625881346720901235)
              ·
                refine ⟨19896897938822020081351853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13264598625881346720901235 19896897938822020081351853)
                ·
                  refine ⟨7461336727058257530506945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19896897938822020081351853 7461336727058257530506945)
                  ·
                    refine ⟨5596002545293693147880209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7461336727058257530506945 5596002545293693147880209)
                    ·
                      refine ⟨4197001908970269860910157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5596002545293693147880209 4197001908970269860910157)
                      ·
                        rfl

theorem cell23_8173632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 3, 2, 2].length) (baseStart_8173632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173632 prefixEnd_8173632 := by exact prefixLift 8173632
  have htrace : WordTrace (prefixWord ++ tailWord_8173632) baseStart_8173632 baseEnd_8173632 := by
    simpa [prefixWord, tailWord_8173632, baseEnd_8173632] using wordTrace_append hprefix tailTrace_8173632
  have hstable : (prefixWord ++ tailWord_8173632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173632).length < 2 ^ (prefixWord ++ tailWord_8173632).sum := by decide
  have hdescent : baseEnd_8173632 < baseStart_8173632 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173681 : List Nat := [1, 2, 2, 2, 1, 1, 4, 2, 2, 6]
def baseStart_8173681 : Nat := 118140960795 + 8173681 * 2 ^ 59
def prefixEnd_8173681 : Nat := 4983230072969 + 3 ^ 40 * 8173681 * 2
def baseEnd_8173681 : Nat := 1399009023174113389732477

theorem tailTrace_8173681 : CollatzResearch.WordTrace tailWord_8173681 prefixEnd_8173681 1399009023174113389732477 := by
  unfold tailWord_8173681
  simp only [CollatzResearch.WordTrace]
  refine ⟨298118637501157165422368897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198745758334104776948245931 298118637501157165422368897)
  ·
    refine ⟨223588978125867874066776673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298118637501157165422368897 223588978125867874066776673)
    ·
      refine ⟨167691733594400905550082505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223588978125867874066776673 167691733594400905550082505)
      ·
        refine ⟨125768800195800679162561879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167691733594400905550082505 125768800195800679162561879)
        ·
          refine ⟨188653200293701018743842819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125768800195800679162561879 188653200293701018743842819)
          ·
            refine ⟨282979800440551528115764229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188653200293701018743842819 282979800440551528115764229)
            ·
              refine ⟨53058712582603411521705793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 282979800440551528115764229 53058712582603411521705793)
              ·
                refine ⟨39794034436952558641279345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53058712582603411521705793 39794034436952558641279345)
                ·
                  refine ⟨29845525827714418980959509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39794034436952558641279345 29845525827714418980959509)
                  ·
                    refine ⟨1399009023174113389732477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29845525827714418980959509 1399009023174113389732477)
                    ·
                      rfl

theorem cell23_8173681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 6].length) (baseStart_8173681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173681 prefixEnd_8173681 := by exact prefixLift 8173681
  have htrace : WordTrace (prefixWord ++ tailWord_8173681) baseStart_8173681 baseEnd_8173681 := by
    simpa [prefixWord, tailWord_8173681, baseEnd_8173681] using wordTrace_append hprefix tailTrace_8173681
  have hstable : (prefixWord ++ tailWord_8173681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173681).length < 2 ^ (prefixWord ++ tailWord_8173681).sum := by decide
  have hdescent : baseEnd_8173681 < baseStart_8173681 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173682 : List Nat := [3, 2, 1, 2, 2, 3, 2, 2, 2, 1, 3]
def baseStart_8173682 : Nat := 118140960795 + 8173682 * 2 ^ 59
def prefixEnd_8173682 : Nat := 4983230072969 + 3 ^ 40 * 8173682 * 2
def baseEnd_8173682 : Nat := 4197027583002994665284927

theorem tailTrace_8173682 : CollatzResearch.WordTrace tailWord_8173682 prefixEnd_8173682 4197027583002994665284927 := by
  unfold tailWord_8173682
  simp only [CollatzResearch.WordTrace]
  refine ⟨74529668493538385648288825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198745782649435695062103533 74529668493538385648288825)
  ·
    refine ⟨55897251370153789236216619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74529668493538385648288825 55897251370153789236216619)
    ·
      refine ⟨83845877055230683854324929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55897251370153789236216619 83845877055230683854324929)
      ·
        refine ⟨62884407791423012890743697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83845877055230683854324929 62884407791423012890743697)
        ·
          refine ⟨47163305843567259668057773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62884407791423012890743697 47163305843567259668057773)
          ·
            refine ⟨17686239691337722375521665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47163305843567259668057773 17686239691337722375521665)
            ·
              refine ⟨13264679768503291781641249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17686239691337722375521665 13264679768503291781641249)
              ·
                refine ⟨9948509826377468836230937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13264679768503291781641249 9948509826377468836230937)
                ·
                  refine ⟨7461382369783101627173203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9948509826377468836230937 7461382369783101627173203)
                  ·
                    refine ⟨11192073554674652440759805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7461382369783101627173203 11192073554674652440759805)
                    ·
                      refine ⟨4197027583002994665284927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11192073554674652440759805 4197027583002994665284927)
                      ·
                        rfl

theorem cell23_8173682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_8173682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173682 prefixEnd_8173682 := by exact prefixLift 8173682
  have htrace : WordTrace (prefixWord ++ tailWord_8173682) baseStart_8173682 baseEnd_8173682 := by
    simpa [prefixWord, tailWord_8173682, baseEnd_8173682] using wordTrace_append hprefix tailTrace_8173682
  have hstable : (prefixWord ++ tailWord_8173682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173682).length < 2 ^ (prefixWord ++ tailWord_8173682).sum := by decide
  have hdescent : baseEnd_8173682 < baseStart_8173682 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173688 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 5, 4, 2]
def baseStart_8173688 : Nat := 118140960795 + 8173688 * 2 ^ 59
def prefixEnd_8173688 : Nat := 4983230072969 + 3 ^ 40 * 8173688 * 2
def baseEnd_8173688 : Nat := 4197030663886921641809899

theorem tailTrace_8173688 : CollatzResearch.WordTrace tailWord_8173688 prefixEnd_8173688 4197030663886921641809899 := by
  unfold tailWord_8173688
  simp only [CollatzResearch.WordTrace]
  refine ⟨149059446406065902808936859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198745928541421203745249145 149059446406065902808936859)
  ·
    refine ⟨223589169609098854213405289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149059446406065902808936859 223589169609098854213405289)
    ·
      refine ⟨167691877206824140660053967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223589169609098854213405289 167691877206824140660053967)
      ·
        refine ⟨251537815810236210990080951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167691877206824140660053967 251537815810236210990080951)
        ·
          refine ⟨377306723715354316485121427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251537815810236210990080951 377306723715354316485121427)
          ·
            refine ⟨565960085573031474727682141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377306723715354316485121427 565960085573031474727682141)
            ·
              refine ⟨212235032089886803022880803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 565960085573031474727682141 212235032089886803022880803)
              ·
                refine ⟨318352548134830204534321205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212235032089886803022880803 318352548134830204534321205)
                ·
                  refine ⟨29845551387640331675092613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 318352548134830204534321205 29845551387640331675092613)
                  ·
                    refine ⟨5596040885182562189079865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29845551387640331675092613 5596040885182562189079865)
                    ·
                      refine ⟨4197030663886921641809899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5596040885182562189079865 4197030663886921641809899)
                      ·
                        rfl

theorem cell23_8173688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 5, 4, 2].length) (baseStart_8173688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173688 prefixEnd_8173688 := by exact prefixLift 8173688
  have htrace : WordTrace (prefixWord ++ tailWord_8173688) baseStart_8173688 baseEnd_8173688 := by
    simpa [prefixWord, tailWord_8173688, baseEnd_8173688] using wordTrace_append hprefix tailTrace_8173688
  have hstable : (prefixWord ++ tailWord_8173688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173688).length < 2 ^ (prefixWord ++ tailWord_8173688).sum := by decide
  have hdescent : baseEnd_8173688 < baseStart_8173688 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173705 : List Nat := [1, 2, 1, 1, 4, 2, 4, 1, 1, 4, 2]
def baseStart_8173705 : Nat := 118140960795 + 8173705 * 2 ^ 59
def prefixEnd_8173705 : Nat := 4983230072969 + 3 ^ 40 * 8173705 * 2
def baseEnd_8173705 : Nat := 4197039393058048075297321

theorem tailTrace_8173705 : CollatzResearch.WordTrace tailWord_8173705 prefixEnd_8173705 4197039393058048075297321 := by
  unfold tailWord_8173705
  simp only [CollatzResearch.WordTrace]
  refine ⟨298119512853070217521242569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198746341902046811680828379 298119512853070217521242569)
  ·
    refine ⟨223589634639802663140931927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298119512853070217521242569 223589634639802663140931927)
    ·
      refine ⟨335384451959703994711397891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223589634639802663140931927 335384451959703994711397891)
      ·
        refine ⟨503076677939555992067096837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335384451959703994711397891 503076677939555992067096837)
        ·
          refine ⟨94326877113666748512580657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 503076677939555992067096837 94326877113666748512580657)
          ·
            refine ⟨70745157835250061384435493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94326877113666748512580657 70745157835250061384435493)
            ·
              refine ⟨13264717094109386509581655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70745157835250061384435493 13264717094109386509581655)
              ·
                refine ⟨19897075641164079764372483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13264717094109386509581655 19897075641164079764372483)
                ·
                  refine ⟨29845613461746119646558725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19897075641164079764372483 29845613461746119646558725)
                  ·
                    refine ⟨5596052524077397433729761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29845613461746119646558725 5596052524077397433729761)
                    ·
                      refine ⟨4197039393058048075297321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5596052524077397433729761 4197039393058048075297321)
                      ·
                        rfl

theorem cell23_8173705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 4, 2].length) (baseStart_8173705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173705 prefixEnd_8173705 := by exact prefixLift 8173705
  have htrace : WordTrace (prefixWord ++ tailWord_8173705) baseStart_8173705 baseEnd_8173705 := by
    simpa [prefixWord, tailWord_8173705, baseEnd_8173705] using wordTrace_append hprefix tailTrace_8173705
  have hstable : (prefixWord ++ tailWord_8173705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173705).length < 2 ^ (prefixWord ++ tailWord_8173705).sum := by decide
  have hdescent : baseEnd_8173705 < baseStart_8173705 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173745 : List Nat := [1, 2, 2, 5, 2, 1, 2, 1, 7]
def baseStart_8173745 : Nat := 118140960795 + 8173745 * 2 ^ 59
def prefixEnd_8173745 : Nat := 4983230072969 + 3 ^ 40 * 8173745 * 2
def baseEnd_8173745 : Nat := 466339992476025324310793

theorem tailTrace_8173745 : CollatzResearch.WordTrace tailWord_8173745 prefixEnd_8173745 466339992476025324310793 := by
  unfold tailWord_8173745
  simp only [CollatzResearch.WordTrace]
  refine ⟨298120971772925304352698689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198747314515283536235132459 298120971772925304352698689)
  ·
    refine ⟨223590728829693978264524017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298120971772925304352698689 223590728829693978264524017)
    ·
      refine ⟨167693046622270483698393013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223590728829693978264524017 167693046622270483698393013)
      ·
        refine ⟨15721223120837857846724345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167693046622270483698393013 15721223120837857846724345)
        ·
          refine ⟨11790917340628393385043259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15721223120837857846724345 11790917340628393385043259)
          ·
            refine ⟨17686376010942590077564889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11790917340628393385043259 17686376010942590077564889)
            ·
              refine ⟨13264782008206942558173667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17686376010942590077564889 13264782008206942558173667)
              ·
                refine ⟨19897173012310413837260501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13264782008206942558173667 19897173012310413837260501)
                ·
                  refine ⟨466339992476025324310793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19897173012310413837260501 466339992476025324310793)
                  ·
                    rfl

theorem cell23_8173745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 7].length) (baseStart_8173745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173745 prefixEnd_8173745 := by exact prefixLift 8173745
  have htrace : WordTrace (prefixWord ++ tailWord_8173745) baseStart_8173745 baseEnd_8173745 := by
    simpa [prefixWord, tailWord_8173745, baseEnd_8173745] using wordTrace_append hprefix tailTrace_8173745
  have hstable : (prefixWord ++ tailWord_8173745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173745).length < 2 ^ (prefixWord ++ tailWord_8173745).sum := by decide
  have hdescent : baseEnd_8173745 < baseStart_8173745 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8173756 : List Nat := [2, 2, 2, 3, 3, 1, 3, 1, 2, 2, 2]
def baseStart_8173756 : Nat := 118140960795 + 8173756 * 2 ^ 59
def prefixEnd_8173756 : Nat := 4983230072969 + 3 ^ 40 * 8173756 * 2
def baseEnd_8173756 : Nat := 4197065580571427375759587

theorem tailTrace_8173756 : CollatzResearch.WordTrace tailWord_8173756 prefixEnd_8173756 4197065580571427375759587 := by
  unfold tailWord_8173756
  simp only [CollatzResearch.WordTrace]
  refine ⟨149060686487942726615674561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198747581983923635487566081 149060686487942726615674561)
  ·
    refine ⟨111795514865957044961755921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149060686487942726615674561 111795514865957044961755921)
    ·
      refine ⟨83846636149467783721316941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111795514865957044961755921 83846636149467783721316941)
      ·
        refine ⟨31442488556050418895493853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83846636149467783721316941 31442488556050418895493853)
        ·
          refine ⟨11790933208518907085810195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31442488556050418895493853 11790933208518907085810195)
          ·
            refine ⟨17686399812778360628715293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11790933208518907085810195 17686399812778360628715293)
            ·
              refine ⟨6632399929791885235768235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17686399812778360628715293 6632399929791885235768235)
              ·
                refine ⟨9948599894687827853652353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6632399929791885235768235 9948599894687827853652353)
                ·
                  refine ⟨7461449921015870890239265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9948599894687827853652353 7461449921015870890239265)
                  ·
                    refine ⟨5596087440761903167679449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7461449921015870890239265 5596087440761903167679449)
                    ·
                      refine ⟨4197065580571427375759587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5596087440761903167679449 4197065580571427375759587)
                      ·
                        rfl

theorem cell23_8173756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_8173756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8173756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8173756 prefixEnd_8173756 := by exact prefixLift 8173756
  have htrace : WordTrace (prefixWord ++ tailWord_8173756) baseStart_8173756 baseEnd_8173756 := by
    simpa [prefixWord, tailWord_8173756, baseEnd_8173756] using wordTrace_append hprefix tailTrace_8173756
  have hstable : (prefixWord ++ tailWord_8173756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8173756).length < 2 ^ (prefixWord ++ tailWord_8173756).sum := by decide
  have hdescent : baseEnd_8173756 < baseStart_8173756 := by decide
  rcases family_descends (prefixWord ++ tailWord_8173756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
