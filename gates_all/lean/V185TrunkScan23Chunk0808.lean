import V185TrunkScan23Chunk0807

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4779301 : List Nat := [1, 3, 1, 2, 4, 2, 3, 2, 5]
def baseStart_4779301 : Nat := 118140960795 + 4779301 * 2 ^ 59
def prefixEnd_4779301 : Nat := 4983230072969 + 3 ^ 40 * 4779301 * 2
def baseEnd_4779301 : Nat := 272675400612656744061989

theorem tailTrace_4779301 : CollatzResearch.WordTrace tailWord_4779301 prefixEnd_4779301 272675400612656744061989 := by
  unfold tailWord_4779301
  simp only [CollatzResearch.WordTrace]
  refine ⟨174315428058416191471753757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116210285372277460981169171 174315428058416191471753757)
  ·
    refine ⟨65368285521906071801907659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174315428058416191471753757 65368285521906071801907659)
    ·
      refine ⟨98052428282859107702861489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65368285521906071801907659 98052428282859107702861489)
      ·
        refine ⟨73539321212144330777146117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98052428282859107702861489 73539321212144330777146117)
        ·
          refine ⟨13788622727277062020714897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73539321212144330777146117 13788622727277062020714897)
          ·
            refine ⟨10341467045457796515536173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13788622727277062020714897 10341467045457796515536173)
            ·
              refine ⟨3878050142046673693326065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10341467045457796515536173 3878050142046673693326065)
              ·
                refine ⟨2908537606535005269994549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3878050142046673693326065 2908537606535005269994549)
                ·
                  refine ⟨272675400612656744061989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2908537606535005269994549 272675400612656744061989)
                  ·
                    rfl

theorem cell23_4779301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 2, 5].length) (baseStart_4779301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779301 prefixEnd_4779301 := by exact prefixLift 4779301
  have htrace : WordTrace (prefixWord ++ tailWord_4779301) baseStart_4779301 baseEnd_4779301 := by
    simpa [prefixWord, tailWord_4779301, baseEnd_4779301] using wordTrace_append hprefix tailTrace_4779301
  have hstable : (prefixWord ++ tailWord_4779301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779301).length < 2 ^ (prefixWord ++ tailWord_4779301).sum := by decide
  have hdescent : baseEnd_4779301 < baseStart_4779301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779337 : List Nat := [1, 2, 1, 1, 2, 3, 2, 3, 1, 4, 3]
def baseStart_4779337 : Nat := 118140960795 + 4779337 * 2 ^ 59
def prefixEnd_4779337 : Nat := 4983230072969 + 3 ^ 40 * 4779337 * 2
def baseEnd_4779337 : Nat := 2454097090817472555707735

theorem tailTrace_4779337 : CollatzResearch.WordTrace tailWord_4779337 prefixEnd_4779337 2454097090817472555707735 := by
  unfold tailWord_4779337
  simp only [CollatzResearch.WordTrace]
  refine ⟨174316741086285769620064265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116211160724190513080042843 174316741086285769620064265)
  ·
    refine ⟨130737555814714327215048199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174316741086285769620064265 130737555814714327215048199)
    ·
      refine ⟨196106333722071490822572299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130737555814714327215048199 196106333722071490822572299)
      ·
        refine ⟨294159500583107236233858449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196106333722071490822572299 294159500583107236233858449)
        ·
          refine ⟨220619625437330427175393837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 294159500583107236233858449 220619625437330427175393837)
          ·
            refine ⟨82732359538998910190772689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 220619625437330427175393837 82732359538998910190772689)
            ·
              refine ⟨62049269654249182643079517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82732359538998910190772689 62049269654249182643079517)
              ·
                refine ⟨23268476120343443491154819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62049269654249182643079517 23268476120343443491154819)
                ·
                  refine ⟨34902714180515165236732229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23268476120343443491154819 34902714180515165236732229)
                  ·
                    refine ⟨6544258908846593481887293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34902714180515165236732229 6544258908846593481887293)
                    ·
                      refine ⟨2454097090817472555707735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6544258908846593481887293 2454097090817472555707735)
                      ·
                        rfl

theorem cell23_4779337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 4, 3].length) (baseStart_4779337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779337 prefixEnd_4779337 := by exact prefixLift 4779337
  have htrace : WordTrace (prefixWord ++ tailWord_4779337) baseStart_4779337 baseEnd_4779337 := by
    simpa [prefixWord, tailWord_4779337, baseEnd_4779337] using wordTrace_append hprefix tailTrace_4779337
  have hstable : (prefixWord ++ tailWord_4779337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779337).length < 2 ^ (prefixWord ++ tailWord_4779337).sum := by decide
  have hdescent : baseEnd_4779337 < baseStart_4779337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779354 : List Nat := [3, 1, 1, 2, 1, 2, 4, 2, 2, 2, 3]
def baseStart_4779354 : Nat := 118140960795 + 4779354 * 2 ^ 59
def prefixEnd_4779354 : Nat := 4983230072969 + 3 ^ 40 * 4779354 * 2
def baseEnd_4779354 : Nat := 2454105819988598989195157

theorem tailTrace_4779354 : CollatzResearch.WordTrace tailWord_4779354 prefixEnd_4779354 2454105819988598989195157 := by
  unfold tailWord_4779354
  simp only [CollatzResearch.WordTrace]
  refine ⟨43579340281806045380858279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116211574084816121015622077 43579340281806045380858279)
  ·
    refine ⟨65369010422709068071287419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43579340281806045380858279 65369010422709068071287419)
    ·
      refine ⟨98053515634063602106931129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65369010422709068071287419 98053515634063602106931129)
      ·
        refine ⟨73540136725547701580198347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98053515634063602106931129 73540136725547701580198347)
        ·
          refine ⟨110310205088321552370297521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73540136725547701580198347 110310205088321552370297521)
          ·
            refine ⟨82732653816241164277723141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110310205088321552370297521 82732653816241164277723141)
            ·
              refine ⟨15512372590545218302073089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82732653816241164277723141 15512372590545218302073089)
              ·
                refine ⟨11634279442908913726554817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15512372590545218302073089 11634279442908913726554817)
                ·
                  refine ⟨8725709582181685294916113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11634279442908913726554817 8725709582181685294916113)
                  ·
                    refine ⟨6544282186636263971187085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8725709582181685294916113 6544282186636263971187085)
                    ·
                      refine ⟨2454105819988598989195157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6544282186636263971187085 2454105819988598989195157)
                      ·
                        rfl

theorem cell23_4779354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 2, 2, 3].length) (baseStart_4779354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779354 prefixEnd_4779354 := by exact prefixLift 4779354
  have htrace : WordTrace (prefixWord ++ tailWord_4779354) baseStart_4779354 baseEnd_4779354 := by
    simpa [prefixWord, tailWord_4779354, baseEnd_4779354] using wordTrace_append hprefix tailTrace_4779354
  have hstable : (prefixWord ++ tailWord_4779354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779354).length < 2 ^ (prefixWord ++ tailWord_4779354).sum := by decide
  have hdescent : baseEnd_4779354 < baseStart_4779354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779387 : List Nat := [1, 1, 1, 1, 1, 6, 1, 3, 3, 5]
def baseStart_4779387 : Nat := 118140960795 + 4779387 * 2 ^ 59
def prefixEnd_4779387 : Nat := 4983230072969 + 3 ^ 40 * 4779387 * 2
def baseEnd_4779387 : Nat := 818040921616732453360835

theorem tailTrace_4779387 : CollatzResearch.WordTrace tailWord_4779387 prefixEnd_4779387 818040921616732453360835 := by
  unfold tailWord_4779387
  simp only [CollatzResearch.WordTrace]
  refine ⟨174318564736104628159384415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116212376490736418772922943 174318564736104628159384415)
  ·
    refine ⟨261477847104156942239076623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174318564736104628159384415 261477847104156942239076623)
    ·
      refine ⟨392216770656235413358614935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261477847104156942239076623 392216770656235413358614935)
      ·
        refine ⟨588325155984353120037922403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 392216770656235413358614935 588325155984353120037922403)
        ·
          refine ⟨882487733976529680056883605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 588325155984353120037922403 882487733976529680056883605)
          ·
            refine ⟨41366612530149828752666419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 882487733976529680056883605 41366612530149828752666419)
            ·
              refine ⟨62049918795224743128999629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41366612530149828752666419 62049918795224743128999629)
              ·
                refine ⟨23268719548209278673374861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62049918795224743128999629 23268719548209278673374861)
                ·
                  refine ⟨8725769830578479502515573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23268719548209278673374861 8725769830578479502515573)
                  ·
                    refine ⟨818040921616732453360835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8725769830578479502515573 818040921616732453360835)
                    ·
                      rfl

theorem cell23_4779387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3, 5].length) (baseStart_4779387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779387 prefixEnd_4779387 := by exact prefixLift 4779387
  have htrace : WordTrace (prefixWord ++ tailWord_4779387) baseStart_4779387 baseEnd_4779387 := by
    simpa [prefixWord, tailWord_4779387, baseEnd_4779387] using wordTrace_append hprefix tailTrace_4779387
  have hstable : (prefixWord ++ tailWord_4779387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779387).length < 2 ^ (prefixWord ++ tailWord_4779387).sum := by decide
  have hdescent : baseEnd_4779387 < baseStart_4779387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779404 : List Nat := [2, 2, 1, 2, 1, 3, 3, 3, 1, 5]
def baseStart_4779404 : Nat := 118140960795 + 4779404 * 2 ^ 59
def prefixEnd_4779404 : Nat := 4983230072969 + 3 ^ 40 * 4779404 * 2
def baseEnd_4779404 : Nat := 818043831340441264523309

theorem tailTrace_4779404 : CollatzResearch.WordTrace tailWord_4779404 prefixEnd_4779404 818043831340441264523309 := by
  unfold tailWord_4779404
  simp only [CollatzResearch.WordTrace]
  refine ⟨87159592388521520031376633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116212789851362026708502177 87159592388521520031376633)
  ·
    refine ⟨65369694291391140023532475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87159592388521520031376633 65369694291391140023532475)
    ·
      refine ⟨98054541437086710035298713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65369694291391140023532475 98054541437086710035298713)
      ·
        refine ⟨73540906077815032526474035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98054541437086710035298713 73540906077815032526474035)
        ·
          refine ⟨110311359116722548789711053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73540906077815032526474035 110311359116722548789711053)
          ·
            refine ⟨41366759668770955796141645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110311359116722548789711053 41366759668770955796141645)
            ·
              refine ⟨15512534875789108423553117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41366759668770955796141645 15512534875789108423553117)
              ·
                refine ⟨5817200578420915658832419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15512534875789108423553117 5817200578420915658832419)
                ·
                  refine ⟨8725800867631373488248629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5817200578420915658832419 8725800867631373488248629)
                  ·
                    refine ⟨818043831340441264523309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8725800867631373488248629 818043831340441264523309)
                    ·
                      rfl

theorem cell23_4779404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 1, 5].length) (baseStart_4779404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779404 prefixEnd_4779404 := by exact prefixLift 4779404
  have htrace : WordTrace (prefixWord ++ tailWord_4779404) baseStart_4779404 baseEnd_4779404 := by
    simpa [prefixWord, tailWord_4779404, baseEnd_4779404] using wordTrace_append hprefix tailTrace_4779404
  have hstable : (prefixWord ++ tailWord_4779404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779404).length < 2 ^ (prefixWord ++ tailWord_4779404).sum := by decide
  have hdescent : baseEnd_4779404 < baseStart_4779404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779418 : List Nat := [3, 1, 1, 4, 1, 1, 1, 6, 1, 1, 3]
def baseStart_4779418 : Nat := 118140960795 + 4779418 * 2 ^ 59
def prefixEnd_4779418 : Nat := 4983230072969 + 3 ^ 40 * 4779418 * 2
def baseEnd_4779418 : Nat := 2454138682750486738794863

theorem tailTrace_4779418 : CollatzResearch.WordTrace tailWord_4779418 prefixEnd_4779418 2454138682750486738794863 := by
  unfold tailWord_4779418
  simp only [CollatzResearch.WordTrace]
  refine ⟨43579923849748080113440727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116213130265994880302508605 43579923849748080113440727)
  ·
    refine ⟨65369885774622120170161091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43579923849748080113440727 65369885774622120170161091)
    ·
      refine ⟨98054828661933180255241637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65369885774622120170161091 98054828661933180255241637)
      ·
        refine ⟨18385280374112471297857807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98054828661933180255241637 18385280374112471297857807)
        ·
          refine ⟨27577920561168706946786711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18385280374112471297857807 27577920561168706946786711)
          ·
            refine ⟨41366880841753060420180067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27577920561168706946786711 41366880841753060420180067)
            ·
              refine ⟨62050321262629590630270101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41366880841753060420180067 62050321262629590630270101)
              ·
                refine ⟨2908608809185762060793911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 62050321262629590630270101 2908608809185762060793911)
                ·
                  refine ⟨4362913213778643091190867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2908608809185762060793911 4362913213778643091190867)
                  ·
                    refine ⟨6544369820667964636786301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4362913213778643091190867 6544369820667964636786301)
                    ·
                      refine ⟨2454138682750486738794863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6544369820667964636786301 2454138682750486738794863)
                      ·
                        rfl

theorem cell23_4779418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_4779418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779418 prefixEnd_4779418 := by exact prefixLift 4779418
  have htrace : WordTrace (prefixWord ++ tailWord_4779418) baseStart_4779418 baseEnd_4779418 := by
    simpa [prefixWord, tailWord_4779418, baseEnd_4779418] using wordTrace_append hprefix tailTrace_4779418
  have hstable : (prefixWord ++ tailWord_4779418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779418).length < 2 ^ (prefixWord ++ tailWord_4779418).sum := by decide
  have hdescent : baseEnd_4779418 < baseStart_4779418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779441 : List Nat := [1, 2, 2, 4, 1, 1, 4, 2, 1, 1, 4]
def baseStart_4779441 : Nat := 118140960795 + 4779441 * 2 ^ 59
def prefixEnd_4779441 : Nat := 4983230072969 + 3 ^ 40 * 4779441 * 2
def baseEnd_4779441 : Nat := 2454150492805540148807257

theorem tailTrace_4779441 : CollatzResearch.WordTrace tailWord_4779441 prefixEnd_4779441 2454150492805540148807257 := by
  unfold tailWord_4779441
  simp only [CollatzResearch.WordTrace]
  refine ⟨174320534277908995381850177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116213689518605996921233451 174320534277908995381850177)
  ·
    refine ⟨130740400708431746536387633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174320534277908995381850177 130740400708431746536387633)
    ·
      refine ⟨98055300531323809902290725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130740400708431746536387633 98055300531323809902290725)
      ·
        refine ⟨18385368849623214356679511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98055300531323809902290725 18385368849623214356679511)
        ·
          refine ⟨27578053274434821535019267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18385368849623214356679511 27578053274434821535019267)
          ·
            refine ⟨41367079911652232302528901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27578053274434821535019267 41367079911652232302528901)
            ·
              refine ⟨7756327483434793556724169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41367079911652232302528901 7756327483434793556724169)
              ·
                refine ⟨5817245612576095167543127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7756327483434793556724169 5817245612576095167543127)
                ·
                  refine ⟨8725868418864142751314691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5817245612576095167543127 8725868418864142751314691)
                  ·
                    refine ⟨13088802628296214126972037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8725868418864142751314691 13088802628296214126972037)
                    ·
                      refine ⟨2454150492805540148807257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13088802628296214126972037 2454150492805540148807257)
                      ·
                        rfl

theorem cell23_4779441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_4779441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779441 prefixEnd_4779441 := by exact prefixLift 4779441
  have htrace : WordTrace (prefixWord ++ tailWord_4779441) baseStart_4779441 baseEnd_4779441 := by
    simpa [prefixWord, tailWord_4779441, baseEnd_4779441] using wordTrace_append hprefix tailTrace_4779441
  have hstable : (prefixWord ++ tailWord_4779441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779441).length < 2 ^ (prefixWord ++ tailWord_4779441).sum := by decide
  have hdescent : baseEnd_4779441 < baseStart_4779441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779447 : List Nat := [1, 1, 3, 1, 3, 2, 3, 9]
def baseStart_4779447 : Nat := 118140960795 + 4779447 * 2 ^ 59
def prefixEnd_4779447 : Nat := 4983230072969 + 3 ^ 40 * 4779447 * 2
def baseEnd_4779447 : Nat := 90894576803313597234527

theorem tailTrace_4779447 : CollatzResearch.WordTrace tailWord_4779447 prefixEnd_4779447 90894576803313597234527 := by
  unfold tailWord_4779447
  simp only [CollatzResearch.WordTrace]
  refine ⟨174320753115887258406568595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116213835410591505604379063 174320753115887258406568595)
  ·
    refine ⟨261481129673830887609852893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174320753115887258406568595 261481129673830887609852893)
    ·
      refine ⟨98055423627686582853694835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 261481129673830887609852893 98055423627686582853694835)
      ·
        refine ⟨147083135441529874280542253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98055423627686582853694835 147083135441529874280542253)
        ·
          refine ⟨55156175790573702855203345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147083135441529874280542253 55156175790573702855203345)
          ·
            refine ⟨41367131842930277141402509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55156175790573702855203345 41367131842930277141402509)
            ·
              refine ⟨15512674441098853928025941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41367131842930277141402509 15512674441098853928025941)
              ·
                refine ⟨90894576803313597234527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15512674441098853928025941 90894576803313597234527)
                ·
                  rfl

theorem cell23_4779447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 9].length) (baseStart_4779447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779447 prefixEnd_4779447 := by exact prefixLift 4779447
  have htrace : WordTrace (prefixWord ++ tailWord_4779447) baseStart_4779447 baseEnd_4779447 := by
    simpa [prefixWord, tailWord_4779447, baseEnd_4779447] using wordTrace_append hprefix tailTrace_4779447
  have hstable : (prefixWord ++ tailWord_4779447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779447).length < 2 ^ (prefixWord ++ tailWord_4779447).sum := by decide
  have hdescent : baseEnd_4779447 < baseStart_4779447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779452 : List Nat := [2, 2, 2, 4, 2, 2, 1, 3, 1, 1, 3]
def baseStart_4779452 : Nat := 118140960795 + 4779452 * 2 ^ 59
def prefixEnd_4779452 : Nat := 4983230072969 + 3 ^ 40 * 4779452 * 2
def baseEnd_4779452 : Nat := 2454156141092739605769707

theorem tailTrace_4779452 : CollatzResearch.WordTrace tailWord_4779452 prefixEnd_4779452 2454156141092739605769707 := by
  unfold tailWord_4779452
  simp only [CollatzResearch.WordTrace]
  refine ⟨87160467740434572130250305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116213956987246096173667073 87160467740434572130250305)
  ·
    refine ⟨65370350805325929097687729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87160467740434572130250305 65370350805325929097687729)
    ·
      refine ⟨49027763103994446823265797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65370350805325929097687729 49027763103994446823265797)
      ·
        refine ⟨9192705581998958779362337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49027763103994446823265797 9192705581998958779362337)
        ·
          refine ⟨6894529186499219084521753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9192705581998958779362337 6894529186499219084521753)
          ·
            refine ⟨5170896889874414313391315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6894529186499219084521753 5170896889874414313391315)
            ·
              refine ⟨7756345334811621470086973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5170896889874414313391315 7756345334811621470086973)
              ·
                refine ⟨2908629500554358051282615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7756345334811621470086973 2908629500554358051282615)
                ·
                  refine ⟨4362944250831537076923923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2908629500554358051282615 4362944250831537076923923)
                  ·
                    refine ⟨6544416376247305615385885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4362944250831537076923923 6544416376247305615385885)
                    ·
                      refine ⟨2454156141092739605769707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6544416376247305615385885 2454156141092739605769707)
                      ·
                        rfl

theorem cell23_4779452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_4779452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779452 prefixEnd_4779452 := by exact prefixLift 4779452
  have htrace : WordTrace (prefixWord ++ tailWord_4779452) baseStart_4779452 baseEnd_4779452 := by
    simpa [prefixWord, tailWord_4779452, baseEnd_4779452] using wordTrace_append hprefix tailTrace_4779452
  have hstable : (prefixWord ++ tailWord_4779452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779452).length < 2 ^ (prefixWord ++ tailWord_4779452).sum := by decide
  have hdescent : baseEnd_4779452 < baseStart_4779452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779454 : List Nat := [4, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4]
def baseStart_4779454 : Nat := 118140960795 + 4779454 * 2 ^ 59
def prefixEnd_4779454 : Nat := 4983230072969 + 3 ^ 40 * 4779454 * 2
def baseEnd_4779454 : Nat := 2454157168054048597944697

theorem tailTrace_4779454 : CollatzResearch.WordTrace tailWord_4779454 prefixEnd_4779454 2454157168054048597944697 := by
  unfold tailWord_4779454
  simp only [CollatzResearch.WordTrace]
  refine ⟨21790126053357737325259177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116214005617907932401382277 21790126053357737325259177)
  ·
    refine ⟨16342594540018302993944383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21790126053357737325259177 16342594540018302993944383)
    ·
      refine ⟨24513891810027454490916575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16342594540018302993944383 24513891810027454490916575)
      ·
        refine ⟨36770837715041181736374863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24513891810027454490916575 36770837715041181736374863)
        ·
          refine ⟨55156256572561772604562295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36770837715041181736374863 55156256572561772604562295)
          ·
            refine ⟨82734384858842658906843443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55156256572561772604562295 82734384858842658906843443)
            ·
              refine ⟨124101577288263988360265165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82734384858842658906843443 124101577288263988360265165)
              ·
                refine ⟨46538091483098995635099437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124101577288263988360265165 46538091483098995635099437)
                ·
                  refine ⟨17451784306162123363162289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46538091483098995635099437 17451784306162123363162289)
                  ·
                    refine ⟨13088838229621592522371717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17451784306162123363162289 13088838229621592522371717)
                    ·
                      refine ⟨2454157168054048597944697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13088838229621592522371717 2454157168054048597944697)
                      ·
                        rfl

theorem cell23_4779454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_4779454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779454 prefixEnd_4779454 := by exact prefixLift 4779454
  have htrace : WordTrace (prefixWord ++ tailWord_4779454) baseStart_4779454 baseEnd_4779454 := by
    simpa [prefixWord, tailWord_4779454, baseEnd_4779454] using wordTrace_append hprefix tailTrace_4779454
  have hstable : (prefixWord ++ tailWord_4779454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779454).length < 2 ^ (prefixWord ++ tailWord_4779454).sum := by decide
  have hdescent : baseEnd_4779454 < baseStart_4779454 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779485 : List Nat := [1, 4, 3, 1, 1, 4, 2, 1, 2, 4]
def baseStart_4779485 : Nat := 118140960795 + 4779485 * 2 ^ 59
def prefixEnd_4779485 : Nat := 4983230072969 + 3 ^ 40 * 4779485 * 2
def baseEnd_4779485 : Nat := 818057695318112658885685

theorem tailTrace_4779485 : CollatzResearch.WordTrace tailWord_4779485 prefixEnd_4779485 818057695318112658885685 := by
  unfold tailWord_4779485
  simp only [CollatzResearch.WordTrace]
  refine ⟨174322139089749590896451909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116214759393166393930967939 174322139089749590896451909)
  ·
    refine ⟨32685401079328048293084733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174322139089749590896451909 32685401079328048293084733)
    ·
      refine ⟨12257025404748018109906775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32685401079328048293084733 12257025404748018109906775)
      ·
        refine ⟨18385538107122027164860163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12257025404748018109906775 18385538107122027164860163)
        ·
          refine ⟨27578307160683040747290245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18385538107122027164860163 27578307160683040747290245)
          ·
            refine ⟨5170932592628070140116921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27578307160683040747290245 5170932592628070140116921)
            ·
              refine ⟨3878199444471052605087691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5170932592628070140116921 3878199444471052605087691)
              ·
                refine ⟨5817299166706578907631537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3878199444471052605087691 5817299166706578907631537)
                ·
                  refine ⟨4362974375029934180723653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5817299166706578907631537 4362974375029934180723653)
                  ·
                    refine ⟨818057695318112658885685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4362974375029934180723653 818057695318112658885685)
                    ·
                      rfl

theorem cell23_4779485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_4779485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779485 prefixEnd_4779485 := by exact prefixLift 4779485
  have htrace : WordTrace (prefixWord ++ tailWord_4779485) baseStart_4779485 baseEnd_4779485 := by
    simpa [prefixWord, tailWord_4779485, baseEnd_4779485] using wordTrace_append hprefix tailTrace_4779485
  have hstable : (prefixWord ++ tailWord_4779485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779485).length < 2 ^ (prefixWord ++ tailWord_4779485).sum := by decide
  have hdescent : baseEnd_4779485 < baseStart_4779485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779507 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 3, 8]
def baseStart_4779507 : Nat := 118140960795 + 4779507 * 2 ^ 59
def prefixEnd_4779507 : Nat := 4983230072969 + 3 ^ 40 * 4779507 * 2
def baseEnd_4779507 : Nat := 818061460842912296860651

theorem tailTrace_4779507 : CollatzResearch.WordTrace tailWord_4779507 prefixEnd_4779507 818061460842912296860651 := by
  unfold tailWord_4779507
  simp only [CollatzResearch.WordTrace]
  refine ⟨174322941495669888653752775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116215294330446592435835183 174322941495669888653752775)
  ·
    refine ⟨261484412243504832980629163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174322941495669888653752775 261484412243504832980629163)
    ·
      refine ⟨392226618365257249470943745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261484412243504832980629163 392226618365257249470943745)
      ·
        refine ⟨294169963773942937103207809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 392226618365257249470943745 294169963773942937103207809)
        ·
          refine ⟨220627472830457202827405857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 294169963773942937103207809 220627472830457202827405857)
          ·
            refine ⟨165470604622842902120554393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220627472830457202827405857 165470604622842902120554393)
            ·
              refine ⟨124102953467132176590415795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165470604622842902120554393 124102953467132176590415795)
              ·
                refine ⟨186154430200698264885623693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124102953467132176590415795 186154430200698264885623693)
                ·
                  refine ⟨69807911325261849332108885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 186154430200698264885623693 69807911325261849332108885)
                  ·
                    refine ⟨818061460842912296860651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 69807911325261849332108885 818061460842912296860651)
                    ·
                      rfl

theorem cell23_4779507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 8].length) (baseStart_4779507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779507 prefixEnd_4779507 := by exact prefixLift 4779507
  have htrace : WordTrace (prefixWord ++ tailWord_4779507) baseStart_4779507 baseEnd_4779507 := by
    simpa [prefixWord, tailWord_4779507, baseEnd_4779507] using wordTrace_append hprefix tailTrace_4779507
  have hstable : (prefixWord ++ tailWord_4779507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779507).length < 2 ^ (prefixWord ++ tailWord_4779507).sum := by decide
  have hdescent : baseEnd_4779507 < baseStart_4779507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779548 : List Nat := [2, 2, 3, 1, 2, 1, 4, 1, 1, 4, 2]
def baseStart_4779548 : Nat := 118140960795 + 4779548 * 2 ^ 59
def prefixEnd_4779548 : Nat := 4983230072969 + 3 ^ 40 * 4779548 * 2
def baseEnd_4779548 : Nat := 2454205435235571230169265

theorem tailTrace_4779548 : CollatzResearch.WordTrace tailWord_4779548 prefixEnd_4779548 2454205435235571230169265 := by
  unfold tailWord_4779548
  simp only [CollatzResearch.WordTrace]
  refine ⟨87162218444260676327997649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116216291259014235103996865 87162218444260676327997649)
  ·
    refine ⟨65371663833195507245998237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87162218444260676327997649 65371663833195507245998237)
    ·
      refine ⟨24514373937448315217249339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65371663833195507245998237 24514373937448315217249339)
      ·
        refine ⟨36771560906172472825874009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24514373937448315217249339 36771560906172472825874009)
        ·
          refine ⟨27578670679629354619405507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36771560906172472825874009 27578670679629354619405507)
          ·
            refine ⟨41368006019444031929108261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27578670679629354619405507 41368006019444031929108261)
            ·
              refine ⟨7756501128645755986707799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41368006019444031929108261 7756501128645755986707799)
              ·
                refine ⟨11634751692968633980061699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7756501128645755986707799 11634751692968633980061699)
                ·
                  refine ⟨17452127539452950970092549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11634751692968633980061699 17452127539452950970092549)
                  ·
                    refine ⟨3272273913647428306892353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17452127539452950970092549 3272273913647428306892353)
                    ·
                      refine ⟨2454205435235571230169265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3272273913647428306892353 2454205435235571230169265)
                      ·
                        rfl

theorem cell23_4779548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 1, 4, 2].length) (baseStart_4779548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779548 prefixEnd_4779548 := by exact prefixLift 4779548
  have htrace : WordTrace (prefixWord ++ tailWord_4779548) baseStart_4779548 baseEnd_4779548 := by
    simpa [prefixWord, tailWord_4779548, baseEnd_4779548] using wordTrace_append hprefix tailTrace_4779548
  have hstable : (prefixWord ++ tailWord_4779548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779548).length < 2 ^ (prefixWord ++ tailWord_4779548).sum := by decide
  have hdescent : baseEnd_4779548 < baseStart_4779548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779554 : List Nat := [3, 3, 1, 1, 1, 1, 3, 1, 9]
def baseStart_4779554 : Nat := 118140960795 + 4779554 * 2 ^ 59
def prefixEnd_4779554 : Nat := 4983230072969 + 3 ^ 40 * 4779554 * 2
def baseEnd_4779554 : Nat := 272689835124388689632693

theorem tailTrace_4779554 : CollatzResearch.WordTrace tailWord_4779554 prefixEnd_4779554 272689835124388689632693 := by
  unfold tailWord_4779554
  simp only [CollatzResearch.WordTrace]
  refine ⟨43581163931624903920178429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116216437150999743787142477 43581163931624903920178429)
  ·
    refine ⟨16342936474359338970066911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43581163931624903920178429 16342936474359338970066911)
    ·
      refine ⟨24514404711539008455100367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16342936474359338970066911 24514404711539008455100367)
      ·
        refine ⟨36771607067308512682650551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24514404711539008455100367 36771607067308512682650551)
        ·
          refine ⟨55157410600962769023975827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36771607067308512682650551 55157410600962769023975827)
          ·
            refine ⟨82736115901444153535963741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55157410600962769023975827 82736115901444153535963741)
            ·
              refine ⟨31026043463041557575986403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82736115901444153535963741 31026043463041557575986403)
              ·
                refine ⟨46539065194562336363979605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31026043463041557575986403 46539065194562336363979605)
                ·
                  refine ⟨272689835124388689632693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 46539065194562336363979605 272689835124388689632693)
                  ·
                    rfl

theorem cell23_4779554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_4779554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779554 prefixEnd_4779554 := by exact prefixLift 4779554
  have htrace : WordTrace (prefixWord ++ tailWord_4779554) baseStart_4779554 baseEnd_4779554 := by
    simpa [prefixWord, tailWord_4779554, baseEnd_4779554] using wordTrace_append hprefix tailTrace_4779554
  have hstable : (prefixWord ++ tailWord_4779554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779554).length < 2 ^ (prefixWord ++ tailWord_4779554).sum := by decide
  have hdescent : baseEnd_4779554 < baseStart_4779554 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779571 : List Nat := [1, 1, 1, 2, 4, 3, 1, 5, 5]
def baseStart_4779571 : Nat := 118140960795 + 4779571 * 2 ^ 59
def prefixEnd_4779571 : Nat := 4983230072969 + 3 ^ 40 * 4779571 * 2
def baseEnd_4779571 : Nat := 272690805032291626686851

theorem tailTrace_4779571 : CollatzResearch.WordTrace tailWord_4779571 prefixEnd_4779571 272690805032291626686851 := by
  unfold tailWord_4779571
  simp only [CollatzResearch.WordTrace]
  refine ⟨174325275767438027584082567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116216850511625351722721711 174325275767438027584082567)
  ·
    refine ⟨261487913651157041376123851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174325275767438027584082567 261487913651157041376123851)
    ·
      refine ⟨392231870476735562064185777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261487913651157041376123851 392231870476735562064185777)
      ·
        refine ⟨294173902857551671548139333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 392231870476735562064185777 294173902857551671548139333)
        ·
          refine ⟨55157606785790938415276125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 294173902857551671548139333 55157606785790938415276125)
          ·
            refine ⟨20684102544671601905728547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55157606785790938415276125 20684102544671601905728547)
            ·
              refine ⟨31026153817007402858592821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20684102544671601905728547 31026153817007402858592821)
              ·
                refine ⟨2908701920344444017993077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31026153817007402858592821 2908701920344444017993077)
                ·
                  refine ⟨272690805032291626686851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2908701920344444017993077 272690805032291626686851)
                  ·
                    rfl

theorem cell23_4779571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 5, 5].length) (baseStart_4779571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779571 prefixEnd_4779571 := by exact prefixLift 4779571
  have htrace : WordTrace (prefixWord ++ tailWord_4779571) baseStart_4779571 baseEnd_4779571 := by
    simpa [prefixWord, tailWord_4779571, baseEnd_4779571] using wordTrace_append hprefix tailTrace_4779571
  have hstable : (prefixWord ++ tailWord_4779571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779571).length < 2 ^ (prefixWord ++ tailWord_4779571).sum := by decide
  have hdescent : baseEnd_4779571 < baseStart_4779571 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779584 : List Nat := [2, 1, 1, 2, 2, 2, 1, 3, 4, 5]
def baseStart_4779584 : Nat := 118140960795 + 4779584 * 2 ^ 59
def prefixEnd_4779584 : Nat := 4983230072969 + 3 ^ 40 * 4779584 * 2
def baseEnd_4779584 : Nat := 818074640179711029773033

theorem tailTrace_4779584 : CollatzResearch.WordTrace tailWord_4779584 prefixEnd_4779584 818074640179711029773033 := by
  unfold tailWord_4779584
  simp only [CollatzResearch.WordTrace]
  refine ⟨87162874958195465402152903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116217166610927287202870537 87162874958195465402152903)
  ·
    refine ⟨130744312437293198103229355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87162874958195465402152903 130744312437293198103229355)
    ·
      refine ⟨196116468655939797154844033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130744312437293198103229355 196116468655939797154844033)
      ·
        refine ⟨147087351491954847866133025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196116468655939797154844033 147087351491954847866133025)
        ·
          refine ⟨110315513618966135899599769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147087351491954847866133025 110315513618966135899599769)
          ·
            refine ⟨82736635214224601924699827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110315513618966135899599769 82736635214224601924699827)
            ·
              refine ⟨124104952821336902887049741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82736635214224601924699827 124104952821336902887049741)
              ·
                refine ⟨46539357308001338582643653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124104952821336902887049741 46539357308001338582643653)
                ·
                  refine ⟨8726129495250250984245685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46539357308001338582643653 8726129495250250984245685)
                  ·
                    refine ⟨818074640179711029773033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8726129495250250984245685 818074640179711029773033)
                    ·
                      rfl

theorem cell23_4779584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 4, 5].length) (baseStart_4779584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779584 prefixEnd_4779584 := by exact prefixLift 4779584
  have htrace : WordTrace (prefixWord ++ tailWord_4779584) baseStart_4779584 baseEnd_4779584 := by
    simpa [prefixWord, tailWord_4779584, baseEnd_4779584] using wordTrace_append hprefix tailTrace_4779584
  have hstable : (prefixWord ++ tailWord_4779584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779584).length < 2 ^ (prefixWord ++ tailWord_4779584).sum := by decide
  have hdescent : baseEnd_4779584 < baseStart_4779584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779594 : List Nat := [3, 1, 2, 1, 1, 3, 2, 1, 1, 1, 7]
def baseStart_4779594 : Nat := 118140960795 + 4779594 * 2 ^ 59
def prefixEnd_4779594 : Nat := 4983230072969 + 3 ^ 40 * 4779594 * 2
def baseEnd_4779594 : Nat := 2454229055345678050194053

theorem tailTrace_4779594 : CollatzResearch.WordTrace tailWord_4779594 prefixEnd_4779594 2454229055345678050194053 := by
  unfold tailWord_4779594
  simp only [CollatzResearch.WordTrace]
  refine ⟨43581528661588675628042459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116217409764236468341446557 43581528661588675628042459)
  ·
    refine ⟨65372292992383013442063689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43581528661588675628042459 65372292992383013442063689)
    ·
      refine ⟨49029219744287260081547767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65372292992383013442063689 49029219744287260081547767)
      ·
        refine ⟨73543829616430890122321651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49029219744287260081547767 73543829616430890122321651)
        ·
          refine ⟨110315744424646335183482477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73543829616430890122321651 110315744424646335183482477)
          ·
            refine ⟨41368404159242375693805929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110315744424646335183482477 41368404159242375693805929)
            ·
              refine ⟨31026303119431781770354447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41368404159242375693805929 31026303119431781770354447)
              ·
                refine ⟨46539454679147672655531671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31026303119431781770354447 46539454679147672655531671)
                ·
                  refine ⟨69809182018721508983297507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46539454679147672655531671 69809182018721508983297507)
                  ·
                    refine ⟨104713773028082263474946261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69809182018721508983297507 104713773028082263474946261)
                    ·
                      refine ⟨2454229055345678050194053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 104713773028082263474946261 2454229055345678050194053)
                      ·
                        rfl

theorem cell23_4779594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_4779594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779594 prefixEnd_4779594 := by exact prefixLift 4779594
  have htrace : WordTrace (prefixWord ++ tailWord_4779594) baseStart_4779594 baseEnd_4779594 := by
    simpa [prefixWord, tailWord_4779594, baseEnd_4779594] using wordTrace_append hprefix tailTrace_4779594
  have hstable : (prefixWord ++ tailWord_4779594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779594).length < 2 ^ (prefixWord ++ tailWord_4779594).sum := by decide
  have hdescent : baseEnd_4779594 < baseStart_4779594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779621 : List Nat := [1, 3, 1, 3, 3, 1, 2, 1, 1, 3, 4]
def baseStart_4779621 : Nat := 118140960795 + 4779621 * 2 ^ 59
def prefixEnd_4779621 : Nat := 4983230072969 + 3 ^ 40 * 4779621 * 2
def baseEnd_4779621 : Nat := 2454242919323349444556429

theorem tailTrace_4779621 : CollatzResearch.WordTrace tailWord_4779621 prefixEnd_4779621 2454242919323349444556429 := by
  unfold tailWord_4779621
  simp only [CollatzResearch.WordTrace]
  refine ⟨174327099417256886123402717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116218066278171257415601811 174327099417256886123402717)
  ·
    refine ⟨65372662281471332296276019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174327099417256886123402717 65372662281471332296276019)
    ·
      refine ⟨98058993422206998444414029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65372662281471332296276019 98058993422206998444414029)
      ·
        refine ⟨36772122533327624416655261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98058993422206998444414029 36772122533327624416655261)
        ·
          refine ⟨13789545949997859156245723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36772122533327624416655261 13789545949997859156245723)
          ·
            refine ⟨20684318924996788734368585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13789545949997859156245723 20684318924996788734368585)
            ·
              refine ⟨15513239193747591550776439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20684318924996788734368585 15513239193747591550776439)
              ·
                refine ⟨23269858790621387326164659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15513239193747591550776439 23269858790621387326164659)
                ·
                  refine ⟨34904788185932080989246989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23269858790621387326164659 34904788185932080989246989)
                  ·
                    refine ⟨13089295569724530370967621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34904788185932080989246989 13089295569724530370967621)
                    ·
                      refine ⟨2454242919323349444556429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13089295569724530370967621 2454242919323349444556429)
                      ·
                        rfl

theorem cell23_4779621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_4779621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779621 prefixEnd_4779621 := by exact prefixLift 4779621
  have htrace : WordTrace (prefixWord ++ tailWord_4779621) baseStart_4779621 baseEnd_4779621 := by
    simpa [prefixWord, tailWord_4779621, baseEnd_4779621] using wordTrace_append hprefix tailTrace_4779621
  have hstable : (prefixWord ++ tailWord_4779621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779621).length < 2 ^ (prefixWord ++ tailWord_4779621).sum := by decide
  have hdescent : baseEnd_4779621 < baseStart_4779621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779638 : List Nat := [5, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4]
def baseStart_4779638 : Nat := 118140960795 + 4779638 * 2 ^ 59
def prefixEnd_4779638 : Nat := 4983230072969 + 3 ^ 40 * 4779638 * 2
def baseEnd_4779638 : Nat := 2454251648494475878043851

theorem tailTrace_4779638 : CollatzResearch.WordTrace tailWord_4779638 prefixEnd_4779638 2454251648494475878043851 := by
  unfold tailWord_4779638
  simp only [CollatzResearch.WordTrace]
  refine ⟨10895482466137206126673223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116218479638796865351181045 10895482466137206126673223)
  ·
    refine ⟨16343223699205809190009835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10895482466137206126673223 16343223699205809190009835)
    ·
      refine ⟨24514835548808713785014753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16343223699205809190009835 24514835548808713785014753)
      ·
        refine ⟨18386126661606535338761065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24514835548808713785014753 18386126661606535338761065)
        ·
          refine ⟨13789594996204901504070799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18386126661606535338761065 13789594996204901504070799)
          ·
            refine ⟨20684392494307352256106199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13789594996204901504070799 20684392494307352256106199)
            ·
              refine ⟨31026588741461028384159299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20684392494307352256106199 31026588741461028384159299)
              ·
                refine ⟨46539883112191542576238949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31026588741461028384159299 46539883112191542576238949)
                ·
                  refine ⟨8726228083535914233044803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46539883112191542576238949 8726228083535914233044803)
                  ·
                    refine ⟨13089342125303871349567205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8726228083535914233044803 13089342125303871349567205)
                    ·
                      refine ⟨2454251648494475878043851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13089342125303871349567205 2454251648494475878043851)
                      ·
                        rfl

theorem cell23_4779638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_4779638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779638 prefixEnd_4779638 := by exact prefixLift 4779638
  have htrace : WordTrace (prefixWord ++ tailWord_4779638) baseStart_4779638 baseEnd_4779638 := by
    simpa [prefixWord, tailWord_4779638, baseEnd_4779638] using wordTrace_append hprefix tailTrace_4779638
  have hstable : (prefixWord ++ tailWord_4779638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779638).length < 2 ^ (prefixWord ++ tailWord_4779638).sum := by decide
  have hdescent : baseEnd_4779638 < baseStart_4779638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779664 : List Nat := [2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 6]
def baseStart_4779664 : Nat := 118140960795 + 4779664 * 2 ^ 59
def prefixEnd_4779664 : Nat := 4983230072969 + 3 ^ 40 * 4779664 * 2
def baseEnd_4779664 : Nat := 2454264998991492776318731

theorem tailTrace_4779664 : CollatzResearch.WordTrace tailWord_4779664 prefixEnd_4779664 2454264998991492776318731 := by
  unfold tailWord_4779664
  simp only [CollatzResearch.WordTrace]
  refine ⟨87164333878050552233609023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116219111837400736311478697 87164333878050552233609023)
  ·
    refine ⟨130746500817075828350413535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87164333878050552233609023 130746500817075828350413535)
    ·
      refine ⟨196119751225613742525620303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130746500817075828350413535 196119751225613742525620303)
      ·
        refine ⟨294179626838420613788430455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196119751225613742525620303 294179626838420613788430455)
        ·
          refine ⟨441269440257630920682645683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294179626838420613788430455 441269440257630920682645683)
          ·
            refine ⟨661904160386446381023968525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 441269440257630920682645683 661904160386446381023968525)
            ·
              refine ⟨248214060144917392883988197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 661904160386446381023968525 248214060144917392883988197)
              ·
                refine ⟨46540136277172011165747787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 248214060144917392883988197 46540136277172011165747787)
                ·
                  refine ⟨69810204415758016748621681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46540136277172011165747787 69810204415758016748621681)
                  ·
                    refine ⟨52357653311818512561466261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 69810204415758016748621681 52357653311818512561466261)
                    ·
                      refine ⟨2454264998991492776318731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52357653311818512561466261 2454264998991492776318731)
                      ·
                        rfl

theorem cell23_4779664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 6].length) (baseStart_4779664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779664 prefixEnd_4779664 := by exact prefixLift 4779664
  have htrace : WordTrace (prefixWord ++ tailWord_4779664) baseStart_4779664 baseEnd_4779664 := by
    simpa [prefixWord, tailWord_4779664, baseEnd_4779664] using wordTrace_append hprefix tailTrace_4779664
  have hstable : (prefixWord ++ tailWord_4779664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779664).length < 2 ^ (prefixWord ++ tailWord_4779664).sum := by decide
  have hdescent : baseEnd_4779664 < baseStart_4779664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779711 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 5, 1, 4]
def baseStart_4779711 : Nat := 118140960795 + 4779711 * 2 ^ 59
def prefixEnd_4779711 : Nat := 4983230072969 + 3 ^ 40 * 4779711 * 2
def baseEnd_4779711 : Nat := 2454289132582254092431015

theorem tailTrace_4779711 : CollatzResearch.WordTrace tailWord_4779711 prefixEnd_4779711 2454289132582254092431015 := by
  unfold tailWord_4779711
  simp only [CollatzResearch.WordTrace]
  refine ⟨174330381986930831494178987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116220254657953887662785991 174330381986930831494178987)
  ·
    refine ⟨261495572980396247241268481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174330381986930831494178987 261495572980396247241268481)
    ·
      refine ⟨196121679735297185430951361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261495572980396247241268481 196121679735297185430951361)
      ·
        refine ⟨147091259801472889073213521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196121679735297185430951361 147091259801472889073213521)
        ·
          refine ⟨110318444851104666804910141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147091259801472889073213521 110318444851104666804910141)
          ·
            refine ⟨41369416819164250051841303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110318444851104666804910141 41369416819164250051841303)
            ·
              refine ⟨62054125228746375077761955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41369416819164250051841303 62054125228746375077761955)
              ·
                refine ⟨93081187843119562616642933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62054125228746375077761955 93081187843119562616642933)
                ·
                  refine ⟨8726361360292458995310275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 93081187843119562616642933 8726361360292458995310275)
                  ·
                    refine ⟨13089542040438688492965413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8726361360292458995310275 13089542040438688492965413)
                    ·
                      refine ⟨2454289132582254092431015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13089542040438688492965413 2454289132582254092431015)
                      ·
                        rfl

theorem cell23_4779711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5, 1, 4].length) (baseStart_4779711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779711 prefixEnd_4779711 := by exact prefixLift 4779711
  have htrace : WordTrace (prefixWord ++ tailWord_4779711) baseStart_4779711 baseEnd_4779711 := by
    simpa [prefixWord, tailWord_4779711, baseEnd_4779711] using wordTrace_append hprefix tailTrace_4779711
  have hstable : (prefixWord ++ tailWord_4779711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779711).length < 2 ^ (prefixWord ++ tailWord_4779711).sum := by decide
  have hdescent : baseEnd_4779711 < baseStart_4779711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779725 : List Nat := [1, 6, 2, 1, 1, 1, 2, 1, 3, 5]
def baseStart_4779725 : Nat := 118140960795 + 4779725 * 2 ^ 59
def prefixEnd_4779725 : Nat := 4983230072969 + 3 ^ 40 * 4779725 * 2
def baseEnd_4779725 : Nat := 818098773770472345885317

theorem tailTrace_4779725 : CollatzResearch.WordTrace tailWord_4779725 prefixEnd_4779725 818098773770472345885317 := by
  unfold tailWord_4779725
  simp only [CollatzResearch.WordTrace]
  refine ⟨174330892608880111885188629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116220595072586741256792419 174330892608880111885188629)
  ·
    refine ⟨8171760591041255244618217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 174330892608880111885188629 8171760591041255244618217)
    ·
      refine ⟨6128820443280941433463663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8171760591041255244618217 6128820443280941433463663)
      ·
        refine ⟨9193230664921412150195495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6128820443280941433463663 9193230664921412150195495)
        ·
          refine ⟨13789845997382118225293243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9193230664921412150195495 13789845997382118225293243)
          ·
            refine ⟨20684768996073177337939865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13789845997382118225293243 20684768996073177337939865)
            ·
              refine ⟨15513576747054883003454899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20684768996073177337939865 15513576747054883003454899)
              ·
                refine ⟨23270365120582324505182349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15513576747054883003454899 23270365120582324505182349)
                ·
                  refine ⟨8726386920218371689443381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23270365120582324505182349 8726386920218371689443381)
                  ·
                    refine ⟨818098773770472345885317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8726386920218371689443381 818098773770472345885317)
                    ·
                      rfl

theorem cell23_4779725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_4779725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779725 prefixEnd_4779725 := by exact prefixLift 4779725
  have htrace : WordTrace (prefixWord ++ tailWord_4779725) baseStart_4779725 baseEnd_4779725 := by
    simpa [prefixWord, tailWord_4779725, baseEnd_4779725] using wordTrace_append hprefix tailTrace_4779725
  have hstable : (prefixWord ++ tailWord_4779725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779725).length < 2 ^ (prefixWord ++ tailWord_4779725).sum := by decide
  have hdescent : baseEnd_4779725 < baseStart_4779725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779732 : List Nat := [2, 4, 1, 3, 1, 1, 3, 1, 2, 3, 2]
def baseStart_4779732 : Nat := 118140960795 + 4779732 * 2 ^ 59
def prefixEnd_4779732 : Nat := 4983230072969 + 3 ^ 40 * 4779732 * 2
def baseEnd_4779732 : Nat := 2454299915675998510268419

theorem tailTrace_4779732 : CollatzResearch.WordTrace tailWord_4779732 prefixEnd_4779732 2454299915675998510268419 := by
  unfold tailWord_4779732
  simp only [CollatzResearch.WordTrace]
  refine ⟨87165573959927376040346725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116220765279903168053795633 87165573959927376040346725)
  ·
    refine ⟨16343545117486383007565011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87165573959927376040346725 16343545117486383007565011)
    ·
      refine ⟨24515317676229574511347517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16343545117486383007565011 24515317676229574511347517)
      ·
        refine ⟨9193244128586090441755319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24515317676229574511347517 9193244128586090441755319)
        ·
          refine ⟨13789866192879135662632979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9193244128586090441755319 13789866192879135662632979)
          ·
            refine ⟨20684799289318703493949469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13789866192879135662632979 20684799289318703493949469)
            ·
              refine ⟨7756799733494513810231051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20684799289318703493949469 7756799733494513810231051)
              ·
                refine ⟨11635199600241770715346577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7756799733494513810231051 11635199600241770715346577)
                ·
                  refine ⟨8726399700181328036509933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11635199600241770715346577 8726399700181328036509933)
                  ·
                    refine ⟨3272399887567998013691225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8726399700181328036509933 3272399887567998013691225)
                    ·
                      refine ⟨2454299915675998510268419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3272399887567998013691225 2454299915675998510268419)
                      ·
                        rfl

theorem cell23_4779732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_4779732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779732 prefixEnd_4779732 := by exact prefixLift 4779732
  have htrace : WordTrace (prefixWord ++ tailWord_4779732) baseStart_4779732 baseEnd_4779732 := by
    simpa [prefixWord, tailWord_4779732, baseEnd_4779732] using wordTrace_append hprefix tailTrace_4779732
  have hstable : (prefixWord ++ tailWord_4779732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779732).length < 2 ^ (prefixWord ++ tailWord_4779732).sum := by decide
  have hdescent : baseEnd_4779732 < baseStart_4779732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779745 : List Nat := [1, 2, 3, 1, 5, 1, 1, 3, 1, 1, 4]
def baseStart_4779745 : Nat := 118140960795 + 4779745 * 2 ^ 59
def prefixEnd_4779745 : Nat := 4983230072969 + 3 ^ 40 * 4779745 * 2
def baseEnd_4779745 : Nat := 2454306590924506959405859

theorem tailTrace_4779745 : CollatzResearch.WordTrace tailWord_4779745 prefixEnd_4779745 2454306590924506959405859 := by
  unfold tailWord_4779745
  simp only [CollatzResearch.WordTrace]
  refine ⟨174331622068807655300916689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116221081379205103533944459 174331622068807655300916689)
  ·
    refine ⟨130748716551605741475687517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174331622068807655300916689 130748716551605741475687517)
    ·
      refine ⟨49030768706852153053382819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130748716551605741475687517 49030768706852153053382819)
      ·
        refine ⟨73546153060278229580074229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49030768706852153053382819 73546153060278229580074229)
        ·
          refine ⟨6894951849401084023131959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73546153060278229580074229 6894951849401084023131959)
          ·
            refine ⟨10342427774101626034697939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6894951849401084023131959 10342427774101626034697939)
            ·
              refine ⟨15513641661152439052046909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10342427774101626034697939 15513641661152439052046909)
              ·
                refine ⟨5817615622932164644517591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15513641661152439052046909 5817615622932164644517591)
                ·
                  refine ⟨8726423434398246966776387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5817615622932164644517591 8726423434398246966776387)
                  ·
                    refine ⟨13089635151597370450164581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8726423434398246966776387 13089635151597370450164581)
                    ·
                      refine ⟨2454306590924506959405859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13089635151597370450164581 2454306590924506959405859)
                      ·
                        rfl

theorem cell23_4779745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3, 1, 1, 4].length) (baseStart_4779745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779745 prefixEnd_4779745 := by exact prefixLift 4779745
  have htrace : WordTrace (prefixWord ++ tailWord_4779745) baseStart_4779745 baseEnd_4779745 := by
    simpa [prefixWord, tailWord_4779745, baseEnd_4779745] using wordTrace_append hprefix tailTrace_4779745
  have hstable : (prefixWord ++ tailWord_4779745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779745).length < 2 ^ (prefixWord ++ tailWord_4779745).sum := by decide
  have hdescent : baseEnd_4779745 < baseStart_4779745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779762 : List Nat := [3, 2, 1, 3, 1, 1, 4, 1, 3, 2, 2]
def baseStart_4779762 : Nat := 118140960795 + 4779762 * 2 ^ 59
def prefixEnd_4779762 : Nat := 4983230072969 + 3 ^ 40 * 4779762 * 2
def baseEnd_4779762 : Nat := 2454315320095633392893281

theorem tailTrace_4779762 : CollatzResearch.WordTrace tailWord_4779762 prefixEnd_4779762 2454315320095633392893281 := by
  unfold tailWord_4779762
  simp only [CollatzResearch.WordTrace]
  refine ⟨43583060527436516801071385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116221494739830711469523693 43583060527436516801071385)
  ·
    refine ⟨32687295395577387600803539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43583060527436516801071385 32687295395577387600803539)
    ·
      refine ⟨49030943093366081401205309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32687295395577387600803539 49030943093366081401205309)
      ·
        refine ⟨18386603660012280525451991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49030943093366081401205309 18386603660012280525451991)
        ·
          refine ⟨27579905490018420788177987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18386603660012280525451991 27579905490018420788177987)
          ·
            refine ⟨41369858235027631182266981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27579905490018420788177987 41369858235027631182266981)
            ·
              refine ⟨7756848419067680846675059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41369858235027631182266981 7756848419067680846675059)
              ·
                refine ⟨11635272628601521270012589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7756848419067680846675059 11635272628601521270012589)
                ·
                  refine ⟨4363227235725570476254721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11635272628601521270012589 4363227235725570476254721)
                  ·
                    refine ⟨3272420426794177857191041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4363227235725570476254721 3272420426794177857191041)
                    ·
                      refine ⟨2454315320095633392893281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3272420426794177857191041 2454315320095633392893281)
                      ·
                        rfl

theorem cell23_4779762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_4779762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779762 prefixEnd_4779762 := by exact prefixLift 4779762
  have htrace : WordTrace (prefixWord ++ tailWord_4779762) baseStart_4779762 baseEnd_4779762 := by
    simpa [prefixWord, tailWord_4779762, baseEnd_4779762] using wordTrace_append hprefix tailTrace_4779762
  have hstable : (prefixWord ++ tailWord_4779762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779762).length < 2 ^ (prefixWord ++ tailWord_4779762).sum := by decide
  have hdescent : baseEnd_4779762 < baseStart_4779762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779811 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 4, 6]
def baseStart_4779811 : Nat := 118140960795 + 4779811 * 2 ^ 59
def prefixEnd_4779811 : Nat := 4983230072969 + 3 ^ 40 * 4779811 * 2
def baseEnd_4779811 : Nat := 818113493549234567060185

theorem tailTrace_4779811 : CollatzResearch.WordTrace tailWord_4779811 prefixEnd_4779811 818113493549234567060185 := by
  unfold tailWord_4779811
  simp only [CollatzResearch.WordTrace]
  refine ⟨174334029286568548572819287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116222686191045699048546191 174334029286568548572819287)
  ·
    refine ⟨261501043929852822859228931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174334029286568548572819287 261501043929852822859228931)
    ·
      refine ⟨392251565894779234288843397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261501043929852822859228931 392251565894779234288843397)
      ·
        refine ⟨73547168605271106429158137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 392251565894779234288843397 73547168605271106429158137)
        ·
          refine ⟨55160376453953329821868603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73547168605271106429158137 55160376453953329821868603)
          ·
            refine ⟨82740564680929994732802905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55160376453953329821868603 82740564680929994732802905)
            ·
              refine ⟨62055423510697496049602179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82740564680929994732802905 62055423510697496049602179)
              ·
                refine ⟨93083135266046244074403269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62055423510697496049602179 93083135266046244074403269)
                ·
                  refine ⟨17453087862383670763950613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93083135266046244074403269 17453087862383670763950613)
                  ·
                    refine ⟨818113493549234567060185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17453087862383670763950613 818113493549234567060185)
                    ·
                      rfl

theorem cell23_4779811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 6].length) (baseStart_4779811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779811 prefixEnd_4779811 := by exact prefixLift 4779811
  have htrace : WordTrace (prefixWord ++ tailWord_4779811) baseStart_4779811 baseEnd_4779811 := by
    simpa [prefixWord, tailWord_4779811, baseEnd_4779811] using wordTrace_append hprefix tailTrace_4779811
  have hstable : (prefixWord ++ tailWord_4779811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779811).length < 2 ^ (prefixWord ++ tailWord_4779811).sum := by decide
  have hdescent : baseEnd_4779811 < baseStart_4779811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779839 : List Nat := [1, 1, 2, 2, 6, 2, 1, 2, 1, 3, 2]
def baseStart_4779839 : Nat := 118140960795 + 4779839 * 2 ^ 59
def prefixEnd_4779839 : Nat := 4983230072969 + 3 ^ 40 * 4779839 * 2
def baseEnd_4779839 : Nat := 2454354858106029591630427

theorem tailTrace_4779839 : CollatzResearch.WordTrace tailWord_4779839 prefixEnd_4779839 2454354858106029591630427 := by
  unfold tailWord_4779839
  simp only [CollatzResearch.WordTrace]
  refine ⟨174335050530467109354838571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116223367020311406236559047 174335050530467109354838571)
  ·
    refine ⟨261502575795700664032257857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174335050530467109354838571 261502575795700664032257857)
    ·
      refine ⟨196126931846775498024193393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261502575795700664032257857 196126931846775498024193393)
      ·
        refine ⟨147095198885081623518145045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196126931846775498024193393 147095198885081623518145045)
        ·
          refine ⟨6895087447738201102413049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 147095198885081623518145045 6895087447738201102413049)
          ·
            refine ⟨5171315585803650826809787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6895087447738201102413049 5171315585803650826809787)
            ·
              refine ⟨7756973378705476240214681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5171315585803650826809787 7756973378705476240214681)
              ·
                refine ⟨5817730034029107180161011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7756973378705476240214681 5817730034029107180161011)
                ·
                  refine ⟨8726595051043660770241517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5817730034029107180161011 8726595051043660770241517)
                  ·
                    refine ⟨3272473144141372788840569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8726595051043660770241517 3272473144141372788840569)
                    ·
                      refine ⟨2454354858106029591630427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3272473144141372788840569 2454354858106029591630427)
                      ·
                        rfl

theorem cell23_4779839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 2, 1, 3, 2].length) (baseStart_4779839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779839 prefixEnd_4779839 := by exact prefixLift 4779839
  have htrace : WordTrace (prefixWord ++ tailWord_4779839) baseStart_4779839 baseEnd_4779839 := by
    simpa [prefixWord, tailWord_4779839, baseEnd_4779839] using wordTrace_append hprefix tailTrace_4779839
  have hstable : (prefixWord ++ tailWord_4779839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779839).length < 2 ^ (prefixWord ++ tailWord_4779839).sum := by decide
  have hdescent : baseEnd_4779839 < baseStart_4779839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779852 : List Nat := [2, 2, 1, 3, 4, 1, 1, 2, 1, 4, 2]
def baseStart_4779852 : Nat := 118140960795 + 4779852 * 2 ^ 59
def prefixEnd_4779852 : Nat := 4983230072969 + 3 ^ 40 * 4779852 * 2
def baseEnd_4779852 : Nat := 2454361533354538040767867

theorem tailTrace_4779852 : CollatzResearch.WordTrace tailWord_4779852 prefixEnd_4779852 2454361533354538040767867 := by
  unfold tailWord_4779852
  simp only [CollatzResearch.WordTrace]
  refine ⟨87167762339710006287530905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116223683119613341716707873 87167762339710006287530905)
  ·
    refine ⟨65375821754782504715648179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87167762339710006287530905 65375821754782504715648179)
    ·
      refine ⟨98063732632173757073472269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65375821754782504715648179 98063732632173757073472269)
      ·
        refine ⟨36773899737065158902552101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98063732632173757073472269 36773899737065158902552101)
        ·
          refine ⟨6895106200699717294228519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36773899737065158902552101 6895106200699717294228519)
          ·
            refine ⟨10342659301049575941342779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6895106200699717294228519 10342659301049575941342779)
            ·
              refine ⟨15513988951574363912014169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10342659301049575941342779 15513988951574363912014169)
              ·
                refine ⟨11635491713680772934010627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15513988951574363912014169 11635491713680772934010627)
                ·
                  refine ⟨17453237570521159401015941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11635491713680772934010627 17453237570521159401015941)
                  ·
                    refine ⟨3272482044472717387690489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17453237570521159401015941 3272482044472717387690489)
                    ·
                      refine ⟨2454361533354538040767867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3272482044472717387690489 2454361533354538040767867)
                      ·
                        rfl

theorem cell23_4779852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 1, 4, 2].length) (baseStart_4779852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779852 prefixEnd_4779852 := by exact prefixLift 4779852
  have htrace : WordTrace (prefixWord ++ tailWord_4779852) baseStart_4779852 baseEnd_4779852 := by
    simpa [prefixWord, tailWord_4779852, baseEnd_4779852] using wordTrace_append hprefix tailTrace_4779852
  have hstable : (prefixWord ++ tailWord_4779852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779852).length < 2 ^ (prefixWord ++ tailWord_4779852).sum := by decide
  have hdescent : baseEnd_4779852 < baseStart_4779852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779882 : List Nat := [3, 1, 3, 4, 1, 1, 1, 1, 2, 2, 4]
def baseStart_4779882 : Nat := 118140960795 + 4779882 * 2 ^ 59
def prefixEnd_4779882 : Nat := 4983230072969 + 3 ^ 40 * 4779882 * 2
def baseEnd_4779882 : Nat := 2454376937774172923392729

theorem tailTrace_4779882 : CollatzResearch.WordTrace tailWord_4779882 prefixEnd_4779882 2454376937774172923392729 := by
  unfold tailWord_4779882
  simp only [CollatzResearch.WordTrace]
  refine ⟨43584154717327831924663475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116224412579540885132435933 43584154717327831924663475)
  ·
    refine ⟨65376232075991747886995213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43584154717327831924663475 65376232075991747886995213)
    ·
      refine ⟨24516087028496905457623205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65376232075991747886995213 24516087028496905457623205)
      ·
        refine ⟨4596766317843169773304351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24516087028496905457623205 4596766317843169773304351)
        ·
          refine ⟨6895149476764754659956527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4596766317843169773304351 6895149476764754659956527)
          ·
            refine ⟨10342724215147131989934791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6895149476764754659956527 10342724215147131989934791)
            ·
              refine ⟨15514086322720697984902187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10342724215147131989934791 15514086322720697984902187)
              ·
                refine ⟨23271129484081046977353281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15514086322720697984902187 23271129484081046977353281)
                ·
                  refine ⟨17453347113060785233014961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23271129484081046977353281 17453347113060785233014961)
                  ·
                    refine ⟨13090010334795588924761221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17453347113060785233014961 13090010334795588924761221)
                    ·
                      refine ⟨2454376937774172923392729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13090010334795588924761221 2454376937774172923392729)
                      ·
                        rfl

theorem cell23_4779882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_4779882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779882 prefixEnd_4779882 := by exact prefixLift 4779882
  have htrace : WordTrace (prefixWord ++ tailWord_4779882) baseStart_4779882 baseEnd_4779882 := by
    simpa [prefixWord, tailWord_4779882, baseEnd_4779882] using wordTrace_append hprefix tailTrace_4779882
  have hstable : (prefixWord ++ tailWord_4779882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779882).length < 2 ^ (prefixWord ++ tailWord_4779882).sum := by decide
  have hdescent : baseEnd_4779882 < baseStart_4779882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779925 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 4, 4, 2]
def baseStart_4779925 : Nat := 118140960795 + 4779925 * 2 ^ 59
def prefixEnd_4779925 : Nat := 4983230072969 + 3 ^ 40 * 4779925 * 2
def baseEnd_4779925 : Nat := 2454399017442316255155031

theorem tailTrace_4779925 : CollatzResearch.WordTrace tailWord_4779925 prefixEnd_4779925 2454399017442316255155031 := by
  unfold tailWord_4779925
  simp only [CollatzResearch.WordTrace]
  refine ⟨174338187208155546042469229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116225458138770364028312819 174338187208155546042469229)
  ·
    refine ⟨65376820203058329765925961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174338187208155546042469229 65376820203058329765925961)
    ·
      refine ⟨49032615152293747324444471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65376820203058329765925961 49032615152293747324444471)
      ·
        refine ⟨73548922728440620986666707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49032615152293747324444471 73548922728440620986666707)
        ·
          refine ⟨110323384092660931480000061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73548922728440620986666707 110323384092660931480000061)
          ·
            refine ⟨41371269034747849305000023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110323384092660931480000061 41371269034747849305000023)
            ·
              refine ⟨62056903552121773957500035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41371269034747849305000023 62056903552121773957500035)
              ·
                refine ⟨93085355328182660936250053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62056903552121773957500035 93085355328182660936250053)
                ·
                  refine ⟨17453504124034248925546885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93085355328182660936250053 17453504124034248925546885)
                  ·
                    refine ⟨3272532023256421673540041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17453504124034248925546885 3272532023256421673540041)
                    ·
                      refine ⟨2454399017442316255155031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3272532023256421673540041 2454399017442316255155031)
                      ·
                        rfl

theorem cell23_4779925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 4, 2].length) (baseStart_4779925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779925 prefixEnd_4779925 := by exact prefixLift 4779925
  have htrace : WordTrace (prefixWord ++ tailWord_4779925) baseStart_4779925 baseEnd_4779925 := by
    simpa [prefixWord, tailWord_4779925, baseEnd_4779925] using wordTrace_append hprefix tailTrace_4779925
  have hstable : (prefixWord ++ tailWord_4779925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779925).length < 2 ^ (prefixWord ++ tailWord_4779925).sum := by decide
  have hdescent : baseEnd_4779925 < baseStart_4779925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779985 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 3, 5, 2]
def baseStart_4779985 : Nat := 118140960795 + 4779985 * 2 ^ 59
def prefixEnd_4779985 : Nat := 4983230072969 + 3 ^ 40 * 4779985 * 2
def baseEnd_4779985 : Nat := 2454429826281586020404755

theorem tailTrace_4779985 : CollatzResearch.WordTrace tailWord_4779985 prefixEnd_4779985 2454429826281586020404755 := by
  unfold tailWord_4779985
  simp only [CollatzResearch.WordTrace]
  refine ⟨174340375587938176289653409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116226917058625450859768939 174340375587938176289653409)
  ·
    refine ⟨130755281690953632217240057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174340375587938176289653409 130755281690953632217240057)
    ·
      refine ⟨98066461268215224162930043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130755281690953632217240057 98066461268215224162930043)
      ·
        refine ⟨147099691902322836244395065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98066461268215224162930043 147099691902322836244395065)
        ·
          refine ⟨110324768926742127183296299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147099691902322836244395065 110324768926742127183296299)
          ·
            refine ⟨165487153390113190774944449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110324768926742127183296299 165487153390113190774944449)
            ·
              refine ⟨124115365042584893081208337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165487153390113190774944449 124115365042584893081208337)
              ·
                refine ⟨93086523781938669810906253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124115365042584893081208337 93086523781938669810906253)
                ·
                  refine ⟨34907446418227001179089845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93086523781938669810906253 34907446418227001179089845)
                  ·
                    refine ⟨3272573101708781360539673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34907446418227001179089845 3272573101708781360539673)
                    ·
                      refine ⟨2454429826281586020404755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3272573101708781360539673 2454429826281586020404755)
                      ·
                        rfl

theorem cell23_4779985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 5, 2].length) (baseStart_4779985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779985 prefixEnd_4779985 := by exact prefixLift 4779985
  have htrace : WordTrace (prefixWord ++ tailWord_4779985) baseStart_4779985 baseEnd_4779985 := by
    simpa [prefixWord, tailWord_4779985, baseEnd_4779985] using wordTrace_append hprefix tailTrace_4779985
  have hstable : (prefixWord ++ tailWord_4779985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779985).length < 2 ^ (prefixWord ++ tailWord_4779985).sum := by decide
  have hdescent : baseEnd_4779985 < baseStart_4779985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4779986 : List Nat := [3, 2, 2, 3, 3, 1, 1, 1, 3, 4]
def baseStart_4779986 : Nat := 118140960795 + 4779986 * 2 ^ 59
def prefixEnd_4779986 : Nat := 4983230072969 + 3 ^ 40 * 4779986 * 2
def baseEnd_4779986 : Nat := 818143446587413505497417

theorem tailTrace_4779986 : CollatzResearch.WordTrace tailWord_4779986 prefixEnd_4779986 818143446587413505497417 := by
  unfold tailWord_4779986
  simp only [CollatzResearch.WordTrace]
  refine ⟨43585103015233638365109953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116226941373956368973626541 43585103015233638365109953)
  ·
    refine ⟨32688827261425228773832465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43585103015233638365109953 32688827261425228773832465)
    ·
      refine ⟨24516620446068921580374349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32688827261425228773832465 24516620446068921580374349)
      ·
        refine ⟨9193732667275845592640381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24516620446068921580374349 9193732667275845592640381)
        ·
          refine ⟨3447649750228442097240143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9193732667275845592640381 3447649750228442097240143)
          ·
            refine ⟨5171474625342663145860215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3447649750228442097240143 5171474625342663145860215)
            ·
              refine ⟨7757211938013994718790323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5171474625342663145860215 7757211938013994718790323)
              ·
                refine ⟨11635817907020992078185485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7757211938013994718790323 11635817907020992078185485)
                ·
                  refine ⟨4363431715132872029319557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11635817907020992078185485 4363431715132872029319557)
                  ·
                    refine ⟨818143446587413505497417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4363431715132872029319557 818143446587413505497417)
                    ·
                      rfl

theorem cell23_4779986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_4779986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4779986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4779986 prefixEnd_4779986 := by exact prefixLift 4779986
  have htrace : WordTrace (prefixWord ++ tailWord_4779986) baseStart_4779986 baseEnd_4779986 := by
    simpa [prefixWord, tailWord_4779986, baseEnd_4779986] using wordTrace_append hprefix tailTrace_4779986
  have hstable : (prefixWord ++ tailWord_4779986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4779986).length < 2 ^ (prefixWord ++ tailWord_4779986).sum := by decide
  have hdescent : baseEnd_4779986 < baseStart_4779986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4779986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780015 : List Nat := [1, 1, 2, 1, 4, 2, 3, 1, 3, 1, 4]
def baseStart_4780015 : Nat := 118140960795 + 4780015 * 2 ^ 59
def prefixEnd_4780015 : Nat := 4983230072969 + 3 ^ 40 * 4780015 * 2
def baseEnd_4780015 : Nat := 2454445230701220903029617

theorem tailTrace_4780015 : CollatzResearch.WordTrace tailWord_4780015 prefixEnd_4780015 2454445230701220903029617 := by
  unfold tailWord_4780015
  simp only [CollatzResearch.WordTrace]
  refine ⟨174341469777829491413245499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116227646518552994275496999 174341469777829491413245499)
  ·
    refine ⟨261512204666744237119868249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174341469777829491413245499 261512204666744237119868249)
    ·
      refine ⟨196134153500058177839901187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261512204666744237119868249 196134153500058177839901187)
      ·
        refine ⟨294201230250087266759851781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196134153500058177839901187 294201230250087266759851781)
        ·
          refine ⟨55162730671891362517472209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 294201230250087266759851781 55162730671891362517472209)
          ·
            refine ⟨41372048003918521888104157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55162730671891362517472209 41372048003918521888104157)
            ·
              refine ⟨15514518001469445708039059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41372048003918521888104157 15514518001469445708039059)
              ·
                refine ⟨23271777002204168562058589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15514518001469445708039059 23271777002204168562058589)
                ·
                  refine ⟨8726916375826563210771971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23271777002204168562058589 8726916375826563210771971)
                  ·
                    refine ⟨13090374563739844816157957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8726916375826563210771971 13090374563739844816157957)
                    ·
                      refine ⟨2454445230701220903029617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13090374563739844816157957 2454445230701220903029617)
                      ·
                        rfl

theorem cell23_4780015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3, 1, 4].length) (baseStart_4780015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780015 prefixEnd_4780015 := by exact prefixLift 4780015
  have htrace : WordTrace (prefixWord ++ tailWord_4780015) baseStart_4780015 baseEnd_4780015 := by
    simpa [prefixWord, tailWord_4780015, baseEnd_4780015] using wordTrace_append hprefix tailTrace_4780015
  have hstable : (prefixWord ++ tailWord_4780015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780015).length < 2 ^ (prefixWord ++ tailWord_4780015).sum := by decide
  have hdescent : baseEnd_4780015 < baseStart_4780015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780025 : List Nat := [1, 2, 1, 3, 1, 5, 1, 2, 1, 6]
def baseStart_4780025 : Nat := 118140960795 + 4780025 * 2 ^ 59
def prefixEnd_4780025 : Nat := 4983230072969 + 3 ^ 40 * 4780025 * 2
def baseEnd_4780025 : Nat := 818150121835921954634857

theorem tailTrace_4780025 : CollatzResearch.WordTrace tailWord_4780025 prefixEnd_4780025 818150121835921954634857 := by
  unfold tailWord_4780025
  simp only [CollatzResearch.WordTrace]
  refine ⟨174341834507793263121109529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116227889671862175414073019 174341834507793263121109529)
  ·
    refine ⟨130756375880844947340832147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174341834507793263121109529 130756375880844947340832147)
    ·
      refine ⟨196134563821267421011248221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130756375880844947340832147 196134563821267421011248221)
      ·
        refine ⟨73550461432975282879218083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196134563821267421011248221 73550461432975282879218083)
        ·
          refine ⟨110325692149462924318827125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73550461432975282879218083 110325692149462924318827125)
          ·
            refine ⟨10343033639012149154890043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 110325692149462924318827125 10343033639012149154890043)
            ·
              refine ⟨15514550458518223732335065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10343033639012149154890043 15514550458518223732335065)
              ·
                refine ⟨11635912843888667799251299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15514550458518223732335065 11635912843888667799251299)
                ·
                  refine ⟨17453869265833001698876949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11635912843888667799251299 17453869265833001698876949)
                  ·
                    refine ⟨818150121835921954634857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17453869265833001698876949 818150121835921954634857)
                    ·
                      rfl

theorem cell23_4780025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 6].length) (baseStart_4780025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780025 prefixEnd_4780025 := by exact prefixLift 4780025
  have htrace : WordTrace (prefixWord ++ tailWord_4780025) baseStart_4780025 baseEnd_4780025 := by
    simpa [prefixWord, tailWord_4780025, baseEnd_4780025] using wordTrace_append hprefix tailTrace_4780025
  have hstable : (prefixWord ++ tailWord_4780025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780025).length < 2 ^ (prefixWord ++ tailWord_4780025).sum := by decide
  have hdescent : baseEnd_4780025 < baseStart_4780025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780032 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 7, 2, 2]
def baseStart_4780032 : Nat := 118140960795 + 4780032 * 2 ^ 59
def prefixEnd_4780032 : Nat := 4983230072969 + 3 ^ 40 * 4780032 * 2
def baseEnd_4780032 : Nat := 2454453959872347336517039

theorem tailTrace_4780032 : CollatzResearch.WordTrace tailWord_4780032 prefixEnd_4780032 2454453959872347336517039 := by
  unfold tailWord_4780032
  simp only [CollatzResearch.WordTrace]
  refine ⟨87171044909383951658307175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116228059879178602211076233 87171044909383951658307175)
  ·
    refine ⟨130756567364075927487460763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87171044909383951658307175 130756567364075927487460763)
    ·
      refine ⟨196134851046113891231191145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130756567364075927487460763 196134851046113891231191145)
      ·
        refine ⟨147101138284585418423393359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196134851046113891231191145 147101138284585418423393359)
        ·
          refine ⟨220651707426878127635090039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147101138284585418423393359 220651707426878127635090039)
          ·
            refine ⟨330977561140317191452635059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220651707426878127635090039 330977561140317191452635059)
            ·
              refine ⟨496466341710475787178952589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 330977561140317191452635059 496466341710475787178952589)
              ·
                refine ⟨186174878141428420192107221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 496466341710475787178952589 186174878141428420192107221)
                ·
                  refine ⟨4363473706439728598252513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 186174878141428420192107221 4363473706439728598252513)
                  ·
                    refine ⟨3272605279829796448689385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4363473706439728598252513 3272605279829796448689385)
                    ·
                      refine ⟨2454453959872347336517039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3272605279829796448689385 2454453959872347336517039)
                      ·
                        rfl

theorem cell23_4780032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 7, 2, 2].length) (baseStart_4780032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780032 prefixEnd_4780032 := by exact prefixLift 4780032
  have htrace : WordTrace (prefixWord ++ tailWord_4780032) baseStart_4780032 baseEnd_4780032 := by
    simpa [prefixWord, tailWord_4780032, baseEnd_4780032] using wordTrace_append hprefix tailTrace_4780032
  have hstable : (prefixWord ++ tailWord_4780032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780032).length < 2 ^ (prefixWord ++ tailWord_4780032).sum := by decide
  have hdescent : baseEnd_4780032 < baseStart_4780032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780082 : List Nat := [3, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3]
def baseStart_4780082 : Nat := 118140960795 + 4780082 * 2 ^ 59
def prefixEnd_4780082 : Nat := 4983230072969 + 3 ^ 40 * 4780082 * 2
def baseEnd_4780082 : Nat := 2454479633905072140891809

theorem tailTrace_4780082 : CollatzResearch.WordTrace tailWord_4780082 prefixEnd_4780082 2454479633905072140891809 := by
  unfold tailWord_4780082
  simp only [CollatzResearch.WordTrace]
  refine ⟨43585978367146690463983625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116229275645724507903956333 43585978367146690463983625)
  ·
    refine ⟨32689483775360017847987719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43585978367146690463983625 32689483775360017847987719)
    ·
      refine ⟨49034225663040026771981579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32689483775360017847987719 49034225663040026771981579)
      ·
        refine ⟨73551338494560040157972369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49034225663040026771981579 73551338494560040157972369)
        ·
          refine ⟨55163503870920030118479277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73551338494560040157972369 55163503870920030118479277)
          ·
            refine ⟨20686313951595011294429729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55163503870920030118479277 20686313951595011294429729)
            ·
              refine ⟨15514735463696258470822297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20686313951595011294429729 15514735463696258470822297)
              ·
                refine ⟨11636051597772193853116723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15514735463696258470822297 11636051597772193853116723)
                ·
                  refine ⟨17454077396658290779675085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11636051597772193853116723 17454077396658290779675085)
                  ·
                    refine ⟨6545279023746859042378157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17454077396658290779675085 6545279023746859042378157)
                    ·
                      refine ⟨2454479633905072140891809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6545279023746859042378157 2454479633905072140891809)
                      ·
                        rfl

theorem cell23_4780082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3].length) (baseStart_4780082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780082 prefixEnd_4780082 := by exact prefixLift 4780082
  have htrace : WordTrace (prefixWord ++ tailWord_4780082) baseStart_4780082 baseEnd_4780082 := by
    simpa [prefixWord, tailWord_4780082, baseEnd_4780082] using wordTrace_append hprefix tailTrace_4780082
  have hstable : (prefixWord ++ tailWord_4780082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780082).length < 2 ^ (prefixWord ++ tailWord_4780082).sum := by decide
  have hdescent : baseEnd_4780082 < baseStart_4780082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780142 : List Nat := [4, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5]
def baseStart_4780142 : Nat := 118140960795 + 4780142 * 2 ^ 59
def prefixEnd_4780142 : Nat := 4983230072969 + 3 ^ 40 * 4780142 * 2
def baseEnd_4780142 : Nat := 2454510442744341906141533

theorem tailTrace_4780142 : CollatzResearch.WordTrace tailWord_4780142 prefixEnd_4780142 2454510442744341906141533 := by
  unfold tailWord_4780142
  simp only [CollatzResearch.WordTrace]
  refine ⟨21793262731046174012889835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116230734565579594735412453 21793262731046174012889835)
  ·
    refine ⟨32689894096569261019334753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21793262731046174012889835 32689894096569261019334753)
    ·
      refine ⟨24517420572426945764501065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32689894096569261019334753 24517420572426945764501065)
      ·
        refine ⟨18388065429320209323375799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24517420572426945764501065 18388065429320209323375799)
        ·
          refine ⟨27582098143980313985063699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18388065429320209323375799 27582098143980313985063699)
          ·
            refine ⟨41373147215970470977595549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27582098143980313985063699 41373147215970470977595549)
            ·
              refine ⟨15514930205988926616598331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41373147215970470977595549 15514930205988926616598331)
              ·
                refine ⟨23272395308983389924897497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15514930205988926616598331 23272395308983389924897497)
                ·
                  refine ⟨17454296481737542443673123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23272395308983389924897497 17454296481737542443673123)
                  ·
                    refine ⟨26181444722606313665509685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17454296481737542443673123 26181444722606313665509685)
                    ·
                      refine ⟨2454510442744341906141533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26181444722606313665509685 2454510442744341906141533)
                      ·
                        rfl

theorem cell23_4780142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_4780142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780142 prefixEnd_4780142 := by exact prefixLift 4780142
  have htrace : WordTrace (prefixWord ++ tailWord_4780142) baseStart_4780142 baseEnd_4780142 := by
    simpa [prefixWord, tailWord_4780142, baseEnd_4780142] using wordTrace_append hprefix tailTrace_4780142
  have hstable : (prefixWord ++ tailWord_4780142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780142).length < 2 ^ (prefixWord ++ tailWord_4780142).sum := by decide
  have hdescent : baseEnd_4780142 < baseStart_4780142 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780192 : List Nat := [2, 1, 1, 4, 2, 2, 1, 3, 2, 5]
def baseStart_4780192 : Nat := 118140960795 + 4780192 * 2 ^ 59
def prefixEnd_4780192 : Nat := 4983230072969 + 3 ^ 40 * 4780192 * 2
def baseEnd_4780192 : Nat := 818178705592355570172101

theorem tailTrace_4780192 : CollatzResearch.WordTrace tailWord_4780192 prefixEnd_4780192 818178705592355570172101 := by
  unfold tailWord_4780192
  simp only [CollatzResearch.WordTrace]
  refine ⟨87173962749094125321219415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116231950332125500428292553 87173962749094125321219415)
  ·
    refine ⟨130760944123641187981829123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87173962749094125321219415 130760944123641187981829123)
    ·
      refine ⟨196141416185461781972743685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130760944123641187981829123 196141416185461781972743685)
      ·
        refine ⟨36776515534774084119889441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 196141416185461781972743685 36776515534774084119889441)
        ·
          refine ⟨27582386651080563089917081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36776515534774084119889441 27582386651080563089917081)
          ·
            refine ⟨20686789988310422317437811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27582386651080563089917081 20686789988310422317437811)
            ·
              refine ⟨31030184982465633476156717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20686789988310422317437811 31030184982465633476156717)
              ·
                refine ⟨11636319368424612553558769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31030184982465633476156717 11636319368424612553558769)
                ·
                  refine ⟨8727239526318459415169077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11636319368424612553558769 8727239526318459415169077)
                  ·
                    refine ⟨818178705592355570172101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8727239526318459415169077 818178705592355570172101)
                    ·
                      rfl

theorem cell23_4780192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 2, 5].length) (baseStart_4780192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780192 prefixEnd_4780192 := by exact prefixLift 4780192
  have htrace : WordTrace (prefixWord ++ tailWord_4780192) baseStart_4780192 baseEnd_4780192 := by
    simpa [prefixWord, tailWord_4780192, baseEnd_4780192] using wordTrace_append hprefix tailTrace_4780192
  have hstable : (prefixWord ++ tailWord_4780192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780192).length < 2 ^ (prefixWord ++ tailWord_4780192).sum := by decide
  have hdescent : baseEnd_4780192 < baseStart_4780192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780232 : List Nat := [2, 1, 3, 1, 2, 1, 1, 4, 1, 4, 3]
def baseStart_4780232 : Nat := 118140960795 + 4780232 * 2 ^ 59
def prefixEnd_4780232 : Nat := 4983230072969 + 3 ^ 40 * 4780232 * 2
def baseEnd_4780232 : Nat := 2454556656003246554016119

theorem tailTrace_4780232 : CollatzResearch.WordTrace tailWord_4780232 prefixEnd_4780232 2454556656003246554016119 := by
  unfold tailWord_4780232
  simp only [CollatzResearch.WordTrace]
  refine ⟨87174692209021668736947475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116232922945362224982596633 87174692209021668736947475)
  ·
    refine ⟨130762038313532503105421213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87174692209021668736947475 130762038313532503105421213)
    ·
      refine ⟨49035764367574688664532955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130762038313532503105421213 49035764367574688664532955)
      ·
        refine ⟨73553646551362032996799433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49035764367574688664532955 73553646551362032996799433)
        ·
          refine ⟨55165234913521524747599575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73553646551362032996799433 55165234913521524747599575)
          ·
            refine ⟨82747852370282287121399363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55165234913521524747599575 82747852370282287121399363)
            ·
              refine ⟨124121778555423430682099045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82747852370282287121399363 124121778555423430682099045)
              ·
                refine ⟨23272833479141893252893571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 124121778555423430682099045 23272833479141893252893571)
                ·
                  refine ⟨34909250218712839879340357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23272833479141893252893571 34909250218712839879340357)
                  ·
                    refine ⟨6545484416008657477376317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34909250218712839879340357 6545484416008657477376317)
                    ·
                      refine ⟨2454556656003246554016119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6545484416008657477376317 2454556656003246554016119)
                      ·
                        rfl

theorem cell23_4780232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 1, 4, 3].length) (baseStart_4780232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780232 prefixEnd_4780232 := by exact prefixLift 4780232
  have htrace : WordTrace (prefixWord ++ tailWord_4780232) baseStart_4780232 baseEnd_4780232 := by
    simpa [prefixWord, tailWord_4780232, baseEnd_4780232] using wordTrace_append hprefix tailTrace_4780232
  have hstable : (prefixWord ++ tailWord_4780232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780232).length < 2 ^ (prefixWord ++ tailWord_4780232).sum := by decide
  have hdescent : baseEnd_4780232 < baseStart_4780232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780246 : List Nat := [5, 2, 1, 2, 1, 2, 1, 1, 1, 3, 4]
def baseStart_4780246 : Nat := 118140960795 + 4780246 * 2 ^ 59
def prefixEnd_4780246 : Nat := 4983230072969 + 3 ^ 40 * 4780246 * 2
def baseEnd_4780246 : Nat := 2454563844732409499241055

theorem tailTrace_4780246 : CollatzResearch.WordTrace tailWord_4780246 prefixEnd_4780246 2454563844732409499241055 := by
  unfold tailWord_4780246
  simp only [CollatzResearch.WordTrace]
  refine ⟨10896868439999538616556537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116233263359995078576603061 10896868439999538616556537)
  ·
    refine ⟨8172651329999653962417403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10896868439999538616556537 8172651329999653962417403)
    ·
      refine ⟨12258976994999480943626105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8172651329999653962417403 12258976994999480943626105)
      ·
        refine ⟨9194232746249610707719579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12258976994999480943626105 9194232746249610707719579)
        ·
          refine ⟨13791349119374416061579369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9194232746249610707719579 13791349119374416061579369)
          ·
            refine ⟨10343511839530812046184527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13791349119374416061579369 10343511839530812046184527)
            ·
              refine ⟨15515267759296218069276791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10343511839530812046184527 15515267759296218069276791)
              ·
                refine ⟨23272901638944327103915187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15515267759296218069276791 23272901638944327103915187)
                ·
                  refine ⟨34909352458416490655872781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23272901638944327103915187 34909352458416490655872781)
                  ·
                    refine ⟨13091007171906183995952293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34909352458416490655872781 13091007171906183995952293)
                    ·
                      refine ⟨2454563844732409499241055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13091007171906183995952293 2454563844732409499241055)
                      ·
                        rfl

theorem cell23_4780246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_4780246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780246 prefixEnd_4780246 := by exact prefixLift 4780246
  have htrace : WordTrace (prefixWord ++ tailWord_4780246) baseStart_4780246 baseEnd_4780246 := by
    simpa [prefixWord, tailWord_4780246, baseEnd_4780246] using wordTrace_append hprefix tailTrace_4780246
  have hstable : (prefixWord ++ tailWord_4780246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780246).length < 2 ^ (prefixWord ++ tailWord_4780246).sum := by decide
  have hdescent : baseEnd_4780246 < baseStart_4780246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780249 : List Nat := [1, 2, 1, 2, 3, 1, 5, 1, 2, 2, 3]
def baseStart_4780249 : Nat := 118140960795 + 4780249 * 2 ^ 59
def prefixEnd_4780249 : Nat := 4983230072969 + 3 ^ 40 * 4780249 * 2
def baseEnd_4780249 : Nat := 2454565385174372987503541

theorem tailTrace_4780249 : CollatzResearch.WordTrace tailWord_4780249 prefixEnd_4780249 2454565385174372987503541 := by
  unfold tailWord_4780249
  simp only [CollatzResearch.WordTrace]
  refine ⟨174350004458981749377263801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116233336305987832918175867 174350004458981749377263801)
  ·
    refine ⟨130762503344236312032947851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174350004458981749377263801 130762503344236312032947851)
    ·
      refine ⟨196143755016354468049421777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130762503344236312032947851 196143755016354468049421777)
      ·
        refine ⟨147107816262265851037066333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196143755016354468049421777 147107816262265851037066333)
        ·
          refine ⟨55165431098349694138899875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147107816262265851037066333 55165431098349694138899875)
          ·
            refine ⟨82748146647524541208349813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55165431098349694138899875 82748146647524541208349813)
            ·
              refine ⟨7757638748205425738282795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82748146647524541208349813 7757638748205425738282795)
              ·
                refine ⟨11636458122308138607424193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7757638748205425738282795 11636458122308138607424193)
                ·
                  refine ⟨8727343591731103955568145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11636458122308138607424193 8727343591731103955568145)
                  ·
                    refine ⟨6545507693798327966676109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8727343591731103955568145 6545507693798327966676109)
                    ·
                      refine ⟨2454565385174372987503541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6545507693798327966676109 2454565385174372987503541)
                      ·
                        rfl

theorem cell23_4780249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 2, 2, 3].length) (baseStart_4780249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780249 prefixEnd_4780249 := by exact prefixLift 4780249
  have htrace : WordTrace (prefixWord ++ tailWord_4780249) baseStart_4780249 baseEnd_4780249 := by
    simpa [prefixWord, tailWord_4780249, baseEnd_4780249] using wordTrace_append hprefix tailTrace_4780249
  have hstable : (prefixWord ++ tailWord_4780249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780249).length < 2 ^ (prefixWord ++ tailWord_4780249).sum := by decide
  have hdescent : baseEnd_4780249 < baseStart_4780249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780256 : List Nat := [2, 1, 1, 3, 1, 3, 4, 3, 1, 4]
def baseStart_4780256 : Nat := 118140960795 + 4780256 * 2 ^ 59
def prefixEnd_4780256 : Nat := 4983230072969 + 3 ^ 40 * 4780256 * 2
def baseEnd_4780256 : Nat := 818189659846318153372003

theorem tailTrace_4780256 : CollatzResearch.WordTrace tailWord_4780256 prefixEnd_4780256 818189659846318153372003 := by
  unfold tailWord_4780256
  simp only [CollatzResearch.WordTrace]
  refine ⟨87175129884978194786384311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116233506513304259715179081 87175129884978194786384311)
  ·
    refine ⟨130762694827467292179576467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87175129884978194786384311 130762694827467292179576467)
    ·
      refine ⟨196144042241200938269364701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130762694827467292179576467 196144042241200938269364701)
      ·
        refine ⟨73554015840450351851011763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196144042241200938269364701 73554015840450351851011763)
        ·
          refine ⟨110331023760675527776517645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73554015840450351851011763 110331023760675527776517645)
          ·
            refine ⟨41374133910253322916194117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110331023760675527776517645 41374133910253322916194117)
            ·
              refine ⟨7757650108172498046786397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41374133910253322916194117 7757650108172498046786397)
              ·
                refine ⟨2909118790564686767544899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7757650108172498046786397 2909118790564686767544899)
                ·
                  refine ⟨4363678185847030151317349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2909118790564686767544899 4363678185847030151317349)
                  ·
                    refine ⟨818189659846318153372003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4363678185847030151317349 818189659846318153372003)
                    ·
                      rfl

theorem cell23_4780256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 3, 1, 4].length) (baseStart_4780256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780256 prefixEnd_4780256 := by exact prefixLift 4780256
  have htrace : WordTrace (prefixWord ++ tailWord_4780256) baseStart_4780256 baseEnd_4780256 := by
    simpa [prefixWord, tailWord_4780256, baseEnd_4780256] using wordTrace_append hprefix tailTrace_4780256
  have hstable : (prefixWord ++ tailWord_4780256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780256).length < 2 ^ (prefixWord ++ tailWord_4780256).sum := by decide
  have hdescent : baseEnd_4780256 < baseStart_4780256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780269 : List Nat := [1, 5, 1, 2, 3, 1, 1, 1, 8]
def baseStart_4780269 : Nat := 118140960795 + 4780269 * 2 ^ 59
def prefixEnd_4780269 : Nat := 4983230072969 + 3 ^ 40 * 4780269 * 2
def baseEnd_4780269 : Nat := 272730628309718101028161

theorem tailTrace_4780269 : CollatzResearch.WordTrace tailWord_4780269 prefixEnd_4780269 272730628309718101028161 := by
  unfold tailWord_4780269
  simp only [CollatzResearch.WordTrace]
  refine ⟨174350733918909292792991861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116233822612606195195327907 174350733918909292792991861)
  ·
    refine ⟨16345381304897746199342987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 174350733918909292792991861 16345381304897746199342987)
    ·
      refine ⟨24518071957346619299014481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16345381304897746199342987 24518071957346619299014481)
      ·
        refine ⟨18388553968009964474260861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24518071957346619299014481 18388553968009964474260861)
        ·
          refine ⟨6895707738003736677847823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18388553968009964474260861 6895707738003736677847823)
          ·
            refine ⟨10343561607005605016771735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6895707738003736677847823 10343561607005605016771735)
            ·
              refine ⟨15515342410508407525157603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10343561607005605016771735 15515342410508407525157603)
              ·
                refine ⟨23273013615762611287736405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15515342410508407525157603 23273013615762611287736405)
                ·
                  refine ⟨272730628309718101028161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23273013615762611287736405 272730628309718101028161)
                  ·
                    rfl

theorem cell23_4780269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_4780269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780269 prefixEnd_4780269 := by exact prefixLift 4780269
  have htrace : WordTrace (prefixWord ++ tailWord_4780269) baseStart_4780269 baseEnd_4780269 := by
    simpa [prefixWord, tailWord_4780269, baseEnd_4780269] using wordTrace_append hprefix tailTrace_4780269
  have hstable : (prefixWord ++ tailWord_4780269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780269).length < 2 ^ (prefixWord ++ tailWord_4780269).sum := by decide
  have hdescent : baseEnd_4780269 < baseStart_4780269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780286 : List Nat := [4, 2, 2, 1, 1, 1, 5, 1, 6]
def baseStart_4780286 : Nat := 118140960795 + 4780286 * 2 ^ 59
def prefixEnd_4780286 : Nat := 4983230072969 + 3 ^ 40 * 4780286 * 2
def baseEnd_4780286 : Nat := 272731598217621038082319

theorem tailTrace_4780286 : CollatzResearch.WordTrace tailWord_4780286 prefixEnd_4780286 272731598217621038082319 := by
  unfold tailWord_4780286
  simp only [CollatzResearch.WordTrace]
  refine ⟨21793919244980963087045089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116234235973231803130907141 21793919244980963087045089)
  ·
    refine ⟨16345439433735722315283817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21793919244980963087045089 16345439433735722315283817)
    ·
      refine ⟨12259079575301791736462863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16345439433735722315283817 12259079575301791736462863)
      ·
        refine ⟨18388619362952687604694295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12259079575301791736462863 18388619362952687604694295)
        ·
          refine ⟨27582929044429031407041443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18388619362952687604694295 27582929044429031407041443)
          ·
            refine ⟨41374393566643547110562165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27582929044429031407041443 41374393566643547110562165)
            ·
              refine ⟨3878849396872832541615203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41374393566643547110562165 3878849396872832541615203)
              ·
                refine ⟨5818274095309248812422805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3878849396872832541615203 5818274095309248812422805)
                ·
                  refine ⟨272731598217621038082319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5818274095309248812422805 272731598217621038082319)
                  ·
                    rfl

theorem cell23_4780286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_4780286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780286 prefixEnd_4780286 := by exact prefixLift 4780286
  have htrace : WordTrace (prefixWord ++ tailWord_4780286) baseStart_4780286 baseEnd_4780286 := by
    simpa [prefixWord, tailWord_4780286, baseEnd_4780286] using wordTrace_append hprefix tailTrace_4780286
  have hstable : (prefixWord ++ tailWord_4780286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780286).length < 2 ^ (prefixWord ++ tailWord_4780286).sum := by decide
  have hdescent : baseEnd_4780286 < baseStart_4780286 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780289 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 3, 5, 2]
def baseStart_4780289 : Nat := 118140960795 + 4780289 * 2 ^ 59
def prefixEnd_4780289 : Nat := 4983230072969 + 3 ^ 40 * 4780289 * 2
def baseEnd_4780289 : Nat := 2454585924400552831003357

theorem tailTrace_4780289 : CollatzResearch.WordTrace tailWord_4780289 prefixEnd_4780289 2454585924400552831003357 := by
  unfold tailWord_4780289
  simp only [CollatzResearch.WordTrace]
  refine ⟨174351463378836836208719921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116234308919224557472479947 174351463378836836208719921)
  ·
    refine ⟨130763597534127627156539941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174351463378836836208719921 130763597534127627156539941)
    ·
      refine ⟨24518174537648930091851239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130763597534127627156539941 24518174537648930091851239)
      ·
        refine ⟨36777261806473395137776859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24518174537648930091851239 36777261806473395137776859)
        ·
          refine ⟨55165892709710092706665289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36777261806473395137776859 55165892709710092706665289)
          ·
            refine ⟨41374419532282569529998967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55165892709710092706665289 41374419532282569529998967)
            ·
              refine ⟨62061629298423854294998451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41374419532282569529998967 62061629298423854294998451)
              ·
                refine ⟨93092443947635781442497677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62061629298423854294998451 93092443947635781442497677)
                ·
                  refine ⟨34909666480363418040936629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93092443947635781442497677 34909666480363418040936629)
                  ·
                    refine ⟨3272781232534070441337809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34909666480363418040936629 3272781232534070441337809)
                    ·
                      refine ⟨2454585924400552831003357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3272781232534070441337809 2454585924400552831003357)
                      ·
                        rfl

theorem cell23_4780289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 5, 2].length) (baseStart_4780289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780289 prefixEnd_4780289 := by exact prefixLift 4780289
  have htrace : WordTrace (prefixWord ++ tailWord_4780289) baseStart_4780289 baseEnd_4780289 := by
    simpa [prefixWord, tailWord_4780289, baseEnd_4780289] using wordTrace_append hprefix tailTrace_4780289
  have hstable : (prefixWord ++ tailWord_4780289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780289).length < 2 ^ (prefixWord ++ tailWord_4780289).sum := by decide
  have hdescent : baseEnd_4780289 < baseStart_4780289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780296 : List Nat := [2, 1, 3, 2, 3, 1, 2, 2, 3, 1, 3]
def baseStart_4780296 : Nat := 118140960795 + 4780296 * 2 ^ 59
def prefixEnd_4780296 : Nat := 4983230072969 + 3 ^ 40 * 4780296 * 2
def baseEnd_4780296 : Nat := 2454589518765134303615825

theorem tailTrace_4780296 : CollatzResearch.WordTrace tailWord_4780296 prefixEnd_4780296 2454589518765134303615825 := by
  unfold tailWord_4780296
  simp only [CollatzResearch.WordTrace]
  refine ⟨87175859344905738202112371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116234479126540984269483161 87175859344905738202112371)
  ·
    refine ⟨130763789017358607303168557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87175859344905738202112371 130763789017358607303168557)
    ·
      refine ⟨49036420881509477738688209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130763789017358607303168557 49036420881509477738688209)
      ·
        refine ⟨36777315661132108304016157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49036420881509477738688209 36777315661132108304016157)
        ·
          refine ⟨13791493372924540614006059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36777315661132108304016157 13791493372924540614006059)
          ·
            refine ⟨20687240059386810921009089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13791493372924540614006059 20687240059386810921009089)
            ·
              refine ⟨15515430044540108190756817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20687240059386810921009089 15515430044540108190756817)
              ·
                refine ⟨11636572533405081143067613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15515430044540108190756817 11636572533405081143067613)
                ·
                  refine ⟨4363714700026905428650355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11636572533405081143067613 4363714700026905428650355)
                  ·
                    refine ⟨6545572050040358142975533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4363714700026905428650355 6545572050040358142975533)
                    ·
                      refine ⟨2454589518765134303615825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6545572050040358142975533 2454589518765134303615825)
                      ·
                        rfl

theorem cell23_4780296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_4780296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780296 prefixEnd_4780296 := by exact prefixLift 4780296
  have htrace : WordTrace (prefixWord ++ tailWord_4780296) baseStart_4780296 baseEnd_4780296 := by
    simpa [prefixWord, tailWord_4780296, baseEnd_4780296] using wordTrace_append hprefix tailTrace_4780296
  have hstable : (prefixWord ++ tailWord_4780296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780296).length < 2 ^ (prefixWord ++ tailWord_4780296).sum := by decide
  have hdescent : baseEnd_4780296 < baseStart_4780296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780299 : List Nat := [1, 1, 1, 1, 5, 2, 4, 2, 1, 5]
def baseStart_4780299 : Nat := 118140960795 + 4780299 * 2 ^ 59
def prefixEnd_4780299 : Nat := 4983230072969 + 3 ^ 40 * 4780299 * 2
def baseEnd_4780299 : Nat := 818197019735699263959437

theorem tailTrace_4780299 : CollatzResearch.WordTrace tailWord_4780299 prefixEnd_4780299 818197019735699263959437 := by
  unfold tailWord_4780299
  simp only [CollatzResearch.WordTrace]
  refine ⟨174351828108800607916583951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116234552072533738611055967 174351828108800607916583951)
  ·
    refine ⟨261527742163200911874875927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174351828108800607916583951 261527742163200911874875927)
    ·
      refine ⟨392291613244801367812313891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261527742163200911874875927 392291613244801367812313891)
      ·
        refine ⟨588437419867202051718470837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 392291613244801367812313891 588437419867202051718470837)
        ·
          refine ⟨55166008112550192348606641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 588437419867202051718470837 55166008112550192348606641)
          ·
            refine ⟨41374506084412644261454981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55166008112550192348606641 41374506084412644261454981)
            ·
              refine ⟨7757719890827370799022809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41374506084412644261454981 7757719890827370799022809)
              ·
                refine ⟨5818289918120528099267107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7757719890827370799022809 5818289918120528099267107)
                ·
                  refine ⟨8727434877180792148900661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5818289918120528099267107 8727434877180792148900661)
                  ·
                    refine ⟨818197019735699263959437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8727434877180792148900661 818197019735699263959437)
                    ·
                      rfl

theorem cell23_4780299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2, 1, 5].length) (baseStart_4780299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780299 prefixEnd_4780299 := by exact prefixLift 4780299
  have htrace : WordTrace (prefixWord ++ tailWord_4780299) baseStart_4780299 baseEnd_4780299 := by
    simpa [prefixWord, tailWord_4780299, baseEnd_4780299] using wordTrace_append hprefix tailTrace_4780299
  have hstable : (prefixWord ++ tailWord_4780299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780299).length < 2 ^ (prefixWord ++ tailWord_4780299).sum := by decide
  have hdescent : baseEnd_4780299 < baseStart_4780299 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780312 : List Nat := [2, 1, 2, 3, 1, 2, 2, 1, 3, 6]
def baseStart_4780312 : Nat := 118140960795 + 4780312 * 2 ^ 59
def prefixEnd_4780312 : Nat := 4983230072969 + 3 ^ 40 * 4780312 * 2
def baseEnd_4780312 : Nat := 818199244818535413671917

theorem tailTrace_4780312 : CollatzResearch.WordTrace tailWord_4780312 prefixEnd_4780312 818199244818535413671917 := by
  unfold tailWord_4780312
  simp only [CollatzResearch.WordTrace]
  refine ⟨87176151128876755568403595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116234868171835674091204793 87176151128876755568403595)
  ·
    refine ⟨130764226693315133352605393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87176151128876755568403595 130764226693315133352605393)
    ·
      refine ⟨98073170019986350014454045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130764226693315133352605393 98073170019986350014454045)
      ·
        refine ⟨36777438757494881255420267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98073170019986350014454045 36777438757494881255420267)
        ·
          refine ⟨55166158136242321883130401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36777438757494881255420267 55166158136242321883130401)
          ·
            refine ⟨41374618602181741412347801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55166158136242321883130401 41374618602181741412347801)
            ·
              refine ⟨31030963951636306059260851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41374618602181741412347801 31030963951636306059260851)
              ·
                refine ⟨46546445927454459088891277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31030963951636306059260851 46546445927454459088891277)
                ·
                  refine ⟨17454917222795422158334229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46546445927454459088891277 17454917222795422158334229)
                  ·
                    refine ⟨818199244818535413671917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17454917222795422158334229 818199244818535413671917)
                    ·
                      rfl

theorem cell23_4780312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 3, 6].length) (baseStart_4780312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780312 prefixEnd_4780312 := by exact prefixLift 4780312
  have htrace : WordTrace (prefixWord ++ tailWord_4780312) baseStart_4780312 baseEnd_4780312 := by
    simpa [prefixWord, tailWord_4780312, baseEnd_4780312] using wordTrace_append hprefix tailTrace_4780312
  have hstable : (prefixWord ++ tailWord_4780312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780312).length < 2 ^ (prefixWord ++ tailWord_4780312).sum := by decide
  have hdescent : baseEnd_4780312 < baseStart_4780312 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780330 : List Nat := [3, 1, 4, 2, 2, 2, 1, 1, 3, 1, 3]
def baseStart_4780330 : Nat := 118140960795 + 4780330 * 2 ^ 59
def prefixEnd_4780330 : Nat := 4983230072969 + 3 ^ 40 * 4780330 * 2
def baseEnd_4780330 : Nat := 2454606977107387170590669

theorem tailTrace_4780330 : CollatzResearch.WordTrace tailWord_4780330 prefixEnd_4780330 2454606977107387170590669 := by
  unfold tailWord_4780330
  simp only [CollatzResearch.WordTrace]
  refine ⟨43588239692922075052740611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116235305847792200140641629 43588239692922075052740611)
  ·
    refine ⟨65382359539383112579110917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43588239692922075052740611 65382359539383112579110917)
    ·
      refine ⟨12259192413634333608583297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65382359539383112579110917 12259192413634333608583297)
      ·
        refine ⟨9194394310225750206437473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12259192413634333608583297 9194394310225750206437473)
        ·
          refine ⟨6895795732669312654828105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9194394310225750206437473 6895795732669312654828105)
          ·
            refine ⟨5171846799501984491121079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6895795732669312654828105 5171846799501984491121079)
            ·
              refine ⟨7757770199252976736681619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5171846799501984491121079 7757770199252976736681619)
              ·
                refine ⟨11636655298879465105022429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7757770199252976736681619 11636655298879465105022429)
                ·
                  refine ⟨4363745737079799414383411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11636655298879465105022429 4363745737079799414383411)
                  ·
                    refine ⟨6545618605619699121575117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4363745737079799414383411 6545618605619699121575117)
                    ·
                      refine ⟨2454606977107387170590669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6545618605619699121575117 2454606977107387170590669)
                      ·
                        rfl

theorem cell23_4780330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_4780330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780330 prefixEnd_4780330 := by exact prefixLift 4780330
  have htrace : WordTrace (prefixWord ++ tailWord_4780330) baseStart_4780330 baseEnd_4780330 := by
    simpa [prefixWord, tailWord_4780330, baseEnd_4780330] using wordTrace_append hprefix tailTrace_4780330
  have hstable : (prefixWord ++ tailWord_4780330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780330).length < 2 ^ (prefixWord ++ tailWord_4780330).sum := by decide
  have hdescent : baseEnd_4780330 < baseStart_4780330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780332 : List Nat := [2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 6]
def baseStart_4780332 : Nat := 118140960795 + 4780332 * 2 ^ 59
def prefixEnd_4780332 : Nat := 4983230072969 + 3 ^ 40 * 4780332 * 2
def baseEnd_4780332 : Nat := 2454608004068696162765659

theorem tailTrace_4780332 : CollatzResearch.WordTrace tailWord_4780332 prefixEnd_4780332 2454608004068696162765659 := by
  unfold tailWord_4780332
  simp only [CollatzResearch.WordTrace]
  refine ⟨87176515858840527276267625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116235354478454036368356833 87176515858840527276267625)
  ·
    refine ⟨65382386894130395457200719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87176515858840527276267625 65382386894130395457200719)
    ·
      refine ⟨98073580341195593185801079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65382386894130395457200719 98073580341195593185801079)
      ·
        refine ⟨147110370511793389778701619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98073580341195593185801079 147110370511793389778701619)
        ·
          refine ⟨220665555767690084668052429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147110370511793389778701619 220665555767690084668052429)
          ·
            refine ⟨82749583412883781750519661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 220665555767690084668052429 82749583412883781750519661)
            ·
              refine ⟨31031093779831418156444873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82749583412883781750519661 31031093779831418156444873)
              ·
                refine ⟨23273320334873563617333655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31031093779831418156444873 23273320334873563617333655)
                ·
                  refine ⟨34909980502310345426000483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23273320334873563617333655 34909980502310345426000483)
                  ·
                    refine ⟨52364970753465518139000725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34909980502310345426000483 52364970753465518139000725)
                    ·
                      refine ⟨2454608004068696162765659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52364970753465518139000725 2454608004068696162765659)
                      ·
                        rfl

theorem cell23_4780332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 6].length) (baseStart_4780332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780332 prefixEnd_4780332 := by exact prefixLift 4780332
  have htrace : WordTrace (prefixWord ++ tailWord_4780332) baseStart_4780332 baseEnd_4780332 := by
    simpa [prefixWord, tailWord_4780332, baseEnd_4780332] using wordTrace_append hprefix tailTrace_4780332
  have hstable : (prefixWord ++ tailWord_4780332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780332).length < 2 ^ (prefixWord ++ tailWord_4780332).sum := by decide
  have hdescent : baseEnd_4780332 < baseStart_4780332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780336 : List Nat := [2, 1, 1, 1, 2, 2, 2, 5, 3, 2, 2]
def baseStart_4780336 : Nat := 118140960795 + 4780336 * 2 ^ 59
def prefixEnd_4780336 : Nat := 4983230072969 + 3 ^ 40 * 4780336 * 2
def baseEnd_4780336 : Nat := 2454610057991314147115641

theorem tailTrace_4780336 : CollatzResearch.WordTrace tailWord_4780336 prefixEnd_4780336 2454610057991314147115641 := by
  unfold tailWord_4780336
  simp only [CollatzResearch.WordTrace]
  refine ⟨87176588804833281617840431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116235451739777708823787241 87176588804833281617840431)
  ·
    refine ⟨130764883207249922426760647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87176588804833281617840431 130764883207249922426760647)
    ·
      refine ⟨196147324810874883640140971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130764883207249922426760647 196147324810874883640140971)
      ·
        refine ⟨294220987216312325460211457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196147324810874883640140971 294220987216312325460211457)
        ·
          refine ⟨220665740412234244095158593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 294220987216312325460211457 220665740412234244095158593)
          ·
            refine ⟨165499305309175683071368945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220665740412234244095158593 165499305309175683071368945)
            ·
              refine ⟨124124478981881762303526709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165499305309175683071368945 124124478981881762303526709)
              ·
                refine ⟨11636669904551415215955629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 124124478981881762303526709 11636669904551415215955629)
                ·
                  refine ⟨4363751214206780705983361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11636669904551415215955629 4363751214206780705983361)
                  ·
                    refine ⟨3272813410655085529487521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4363751214206780705983361 3272813410655085529487521)
                    ·
                      refine ⟨2454610057991314147115641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3272813410655085529487521 2454610057991314147115641)
                      ·
                        rfl

theorem cell23_4780336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 3, 2, 2].length) (baseStart_4780336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780336 prefixEnd_4780336 := by exact prefixLift 4780336
  have htrace : WordTrace (prefixWord ++ tailWord_4780336) baseStart_4780336 baseEnd_4780336 := by
    simpa [prefixWord, tailWord_4780336, baseEnd_4780336] using wordTrace_append hprefix tailTrace_4780336
  have hstable : (prefixWord ++ tailWord_4780336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780336).length < 2 ^ (prefixWord ++ tailWord_4780336).sum := by decide
  have hdescent : baseEnd_4780336 < baseStart_4780336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780339 : List Nat := [1, 1, 1, 2, 5, 1, 2, 2, 3, 2, 3]
def baseStart_4780339 : Nat := 118140960795 + 4780339 * 2 ^ 59
def prefixEnd_4780339 : Nat := 4983230072969 + 3 ^ 40 * 4780339 * 2
def baseEnd_4780339 : Nat := 2454611598433277635378127

theorem tailTrace_4780339 : CollatzResearch.WordTrace tailWord_4780339 prefixEnd_4780339 2454611598433277635378127 := by
  unfold tailWord_4780339
  simp only [CollatzResearch.WordTrace]
  refine ⟨174353287028655694748040071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116235524685770463165360047 174353287028655694748040071)
  ·
    refine ⟨261529930542983542122060107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174353287028655694748040071 261529930542983542122060107)
    ·
      refine ⟨392294895814475313183090161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261529930542983542122060107 392294895814475313183090161)
      ·
        refine ⟨294221171860856484887317621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 392294895814475313183090161 294221171860856484887317621)
        ·
          refine ⟨27583234861955295458186027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 294221171860856484887317621 27583234861955295458186027)
          ·
            refine ⟨41374852292932943187279041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27583234861955295458186027 41374852292932943187279041)
            ·
              refine ⟨31031139219699707390459281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41374852292932943187279041 31031139219699707390459281)
              ·
                refine ⟨23273354414774780542844461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31031139219699707390459281 23273354414774780542844461)
                ·
                  refine ⟨8727507905540542703566673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23273354414774780542844461 8727507905540542703566673)
                  ·
                    refine ⟨6545630929155407027675005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8727507905540542703566673 6545630929155407027675005)
                    ·
                      refine ⟨2454611598433277635378127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6545630929155407027675005 2454611598433277635378127)
                      ·
                        rfl

theorem cell23_4780339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3, 2, 3].length) (baseStart_4780339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780339 prefixEnd_4780339 := by exact prefixLift 4780339
  have htrace : WordTrace (prefixWord ++ tailWord_4780339) baseStart_4780339 baseEnd_4780339 := by
    simpa [prefixWord, tailWord_4780339, baseEnd_4780339] using wordTrace_append hprefix tailTrace_4780339
  have hstable : (prefixWord ++ tailWord_4780339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780339).length < 2 ^ (prefixWord ++ tailWord_4780339).sum := by decide
  have hdescent : baseEnd_4780339 < baseStart_4780339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780346 : List Nat := [3, 1, 1, 1, 4, 3, 1, 3, 2, 4]
def baseStart_4780346 : Nat := 118140960795 + 4780346 * 2 ^ 59
def prefixEnd_4780346 : Nat := 4983230072969 + 3 ^ 40 * 4780346 * 2
def baseEnd_4780346 : Nat := 818205064265953035996865

theorem tailTrace_4780346 : CollatzResearch.WordTrace tailWord_4780346 prefixEnd_4780346 818205064265953035996865 := by
  unfold tailWord_4780346
  simp only [CollatzResearch.WordTrace]
  refine ⟨43588385584907583735886223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116235694893086889962363261 43588385584907583735886223)
  ·
    refine ⟨65382578377361375603829335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43588385584907583735886223 65382578377361375603829335)
    ·
      refine ⟨98073867566042063405744003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65382578377361375603829335 98073867566042063405744003)
      ·
        refine ⟨147110801349063095108616005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98073867566042063405744003 147110801349063095108616005)
        ·
          refine ⟨27583275252949330332865501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147110801349063095108616005 27583275252949330332865501)
          ·
            refine ⟨10343728219855998874824563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27583275252949330332865501 10343728219855998874824563)
            ·
              refine ⟨15515592329783998312236845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10343728219855998874824563 15515592329783998312236845)
              ·
                refine ⟨5818347123668999367088817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15515592329783998312236845 5818347123668999367088817)
                ·
                  refine ⟨4363760342751749525316613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5818347123668999367088817 4363760342751749525316613)
                  ·
                    refine ⟨818205064265953035996865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4363760342751749525316613 818205064265953035996865)
                    ·
                      rfl

theorem cell23_4780346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3, 2, 4].length) (baseStart_4780346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780346 prefixEnd_4780346 := by exact prefixLift 4780346
  have htrace : WordTrace (prefixWord ++ tailWord_4780346) baseStart_4780346 baseEnd_4780346 := by
    simpa [prefixWord, tailWord_4780346, baseEnd_4780346] using wordTrace_append hprefix tailTrace_4780346
  have hstable : (prefixWord ++ tailWord_4780346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780346).length < 2 ^ (prefixWord ++ tailWord_4780346).sum := by decide
  have hdescent : baseEnd_4780346 < baseStart_4780346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780369 : List Nat := [1, 2, 2, 1, 4, 2, 1, 1, 3, 3, 3]
def baseStart_4780369 : Nat := 118140960795 + 4780369 * 2 ^ 59
def prefixEnd_4780369 : Nat := 4983230072969 + 3 ^ 40 * 4780369 * 2
def baseEnd_4780369 : Nat := 2454627002852912518002989

theorem tailTrace_4780369 : CollatzResearch.WordTrace tailWord_4780369 prefixEnd_4780369 2454627002852912518002989 := by
  unfold tailWord_4780369
  simp only [CollatzResearch.WordTrace]
  refine ⟨174354381218547009871632161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116236254145698006581088107 174354381218547009871632161)
  ·
    refine ⟨130765785913910257403724121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174354381218547009871632161 130765785913910257403724121)
    ·
      refine ⟨98074339435432693052793091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130765785913910257403724121 98074339435432693052793091)
      ·
        refine ⟨147111509153149039579189637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98074339435432693052793091 147111509153149039579189637)
        ·
          refine ⟨27583407966215444921098057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147111509153149039579189637 27583407966215444921098057)
          ·
            refine ⟨20687555974661583690823543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27583407966215444921098057 20687555974661583690823543)
            ·
              refine ⟨31031333961992375536235315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20687555974661583690823543 31031333961992375536235315)
              ·
                refine ⟨46547000942988563304352973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31031333961992375536235315 46547000942988563304352973)
                ·
                  refine ⟨17455125353620711239132365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46547000942988563304352973 17455125353620711239132365)
                  ·
                    refine ⟨6545672007607766714674637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17455125353620711239132365 6545672007607766714674637)
                    ·
                      refine ⟨2454627002852912518002989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6545672007607766714674637 2454627002852912518002989)
                      ·
                        rfl

theorem cell23_4780369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 3, 3].length) (baseStart_4780369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780369 prefixEnd_4780369 := by exact prefixLift 4780369
  have htrace : WordTrace (prefixWord ++ tailWord_4780369) baseStart_4780369 baseEnd_4780369 := by
    simpa [prefixWord, tailWord_4780369, baseEnd_4780369] using wordTrace_append hprefix tailTrace_4780369
  have hstable : (prefixWord ++ tailWord_4780369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780369).length < 2 ^ (prefixWord ++ tailWord_4780369).sum := by decide
  have hdescent : baseEnd_4780369 < baseStart_4780369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780373 : List Nat := [1, 3, 2, 2, 5, 1, 1, 1, 1, 1, 5]
def baseStart_4780373 : Nat := 118140960795 + 4780373 * 2 ^ 59
def prefixEnd_4780373 : Nat := 4983230072969 + 3 ^ 40 * 4780373 * 2
def baseEnd_4780373 : Nat := 2454629056775530502352971

theorem tailTrace_4780373 : CollatzResearch.WordTrace tailWord_4780373 prefixEnd_4780373 2454629056775530502352971 := by
  unfold tailWord_4780373
  simp only [CollatzResearch.WordTrace]
  refine ⟨174354527110532518554777773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116236351407021679036518515 174354527110532518554777773)
  ·
    refine ⟨65382947666449694458041665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174354527110532518554777773 65382947666449694458041665)
    ·
      refine ⟨49037210749837270843531249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65382947666449694458041665 49037210749837270843531249)
      ·
        refine ⟨36777908062377953132648437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49037210749837270843531249 36777908062377953132648437)
        ·
          refine ⟨3447928880847933106185791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36777908062377953132648437 3447928880847933106185791)
          ·
            refine ⟨5171893321271899659278687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3447928880847933106185791 5171893321271899659278687)
            ·
              refine ⟨7757839981907849488918031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5171893321271899659278687 7757839981907849488918031)
              ·
                refine ⟨11636759972861774233377047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7757839981907849488918031 11636759972861774233377047)
                ·
                  refine ⟨17455139959292661350065571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11636759972861774233377047 17455139959292661350065571)
                  ·
                    refine ⟨26182709938938992025098357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17455139959292661350065571 26182709938938992025098357)
                    ·
                      refine ⟨2454629056775530502352971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26182709938938992025098357 2454629056775530502352971)
                      ·
                        rfl

theorem cell23_4780373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 1, 1, 5].length) (baseStart_4780373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780373 prefixEnd_4780373 := by exact prefixLift 4780373
  have htrace : WordTrace (prefixWord ++ tailWord_4780373) baseStart_4780373 baseEnd_4780373 := by
    simpa [prefixWord, tailWord_4780373, baseEnd_4780373] using wordTrace_append hprefix tailTrace_4780373
  have hstable : (prefixWord ++ tailWord_4780373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780373).length < 2 ^ (prefixWord ++ tailWord_4780373).sum := by decide
  have hdescent : baseEnd_4780373 < baseStart_4780373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780380 : List Nat := [2, 2, 4, 3, 1, 1, 2, 2, 2, 4]
def baseStart_4780380 : Nat := 118140960795 + 4780380 * 2 ^ 59
def prefixEnd_4780380 : Nat := 4983230072969 + 3 ^ 40 * 4780380 * 2
def baseEnd_4780380 : Nat := 818210883713370658321813

theorem tailTrace_4780380 : CollatzResearch.WordTrace tailWord_4780380 prefixEnd_4780380 818210883713370658321813 := by
  unfold tailWord_4780380
  simp only [CollatzResearch.WordTrace]
  refine ⟨87177391210753579375141297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116236521614338105833521729 87177391210753579375141297)
  ·
    refine ⟨65383043408065184531355973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87177391210753579375141297 65383043408065184531355973)
    ·
      refine ⟨12259320639012222099629245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65383043408065184531355973 12259320639012222099629245)
      ·
        refine ⟨4597245239629583287360967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12259320639012222099629245 4597245239629583287360967)
        ·
          refine ⟨6895867859444374931041451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4597245239629583287360967 6895867859444374931041451)
          ·
            refine ⟨10343801789166562396562177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6895867859444374931041451 10343801789166562396562177)
            ·
              refine ⟨7757851341874921797421633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10343801789166562396562177 7757851341874921797421633)
              ·
                refine ⟨5818388506406191348066225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7757851341874921797421633 5818388506406191348066225)
                ·
                  refine ⟨4363791379804643511049669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5818388506406191348066225 4363791379804643511049669)
                  ·
                    refine ⟨818210883713370658321813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4363791379804643511049669 818210883713370658321813)
                    ·
                      rfl

theorem cell23_4780380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_4780380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780380 prefixEnd_4780380 := by exact prefixLift 4780380
  have htrace : WordTrace (prefixWord ++ tailWord_4780380) baseStart_4780380 baseEnd_4780380 := by
    simpa [prefixWord, tailWord_4780380, baseEnd_4780380] using wordTrace_append hprefix tailTrace_4780380
  have hstable : (prefixWord ++ tailWord_4780380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780380).length < 2 ^ (prefixWord ++ tailWord_4780380).sum := by decide
  have hdescent : baseEnd_4780380 < baseStart_4780380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780430 : List Nat := [4, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2]
def baseStart_4780430 : Nat := 118140960795 + 4780430 * 2 ^ 59
def prefixEnd_4780430 : Nat := 4983230072969 + 3 ^ 40 * 4780430 * 2
def baseEnd_4780430 : Nat := 2454658325172836779340209

theorem tailTrace_4780430 : CollatzResearch.WordTrace tailWord_4780430 prefixEnd_4780430 2454658325172836779340209 := by
  unfold tailWord_4780430
  simp only [CollatzResearch.WordTrace]
  refine ⟨21794575758915752161200343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116237737380884011526401829 21794575758915752161200343)
  ·
    refine ⟨32691863638373628241800515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21794575758915752161200343 32691863638373628241800515)
    ·
      refine ⟨49037795457560442362700773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32691863638373628241800515 49037795457560442362700773)
      ·
        refine ⟨9194586648292582943006395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49037795457560442362700773 9194586648292582943006395)
        ·
          refine ⟨13791879972438874414509593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9194586648292582943006395 13791879972438874414509593)
          ·
            refine ⟨10343909979329155810882195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13791879972438874414509593 10343909979329155810882195)
            ·
              refine ⟨15515864968993733716323293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10343909979329155810882195 15515864968993733716323293)
              ·
                refine ⟨5818449363372650143621235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15515864968993733716323293 5818449363372650143621235)
                ·
                  refine ⟨8727674045058975215431853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5818449363372650143621235 8727674045058975215431853)
                  ·
                    refine ⟨3272877766897115705786945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8727674045058975215431853 3272877766897115705786945)
                    ·
                      refine ⟨2454658325172836779340209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3272877766897115705786945 2454658325172836779340209)
                      ·
                        rfl

theorem cell23_4780430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_4780430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780430 prefixEnd_4780430 := by exact prefixLift 4780430
  have htrace : WordTrace (prefixWord ++ tailWord_4780430) baseStart_4780430 baseEnd_4780430 := by
    simpa [prefixWord, tailWord_4780430, baseEnd_4780430] using wordTrace_append hprefix tailTrace_4780430
  have hstable : (prefixWord ++ tailWord_4780430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780430).length < 2 ^ (prefixWord ++ tailWord_4780430).sum := by decide
  have hdescent : baseEnd_4780430 < baseStart_4780430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780439 : List Nat := [1, 1, 3, 3, 1, 1, 3, 2, 2, 2, 4]
def baseStart_4780439 : Nat := 118140960795 + 4780439 * 2 ^ 59
def prefixEnd_4780439 : Nat := 4983230072969 + 3 ^ 40 * 4780439 * 2
def baseEnd_4780439 : Nat := 2454662946498727244127667

theorem tailTrace_4780439 : CollatzResearch.WordTrace tailWord_4780439 prefixEnd_4780439 2454662946498727244127667 := by
  unfold tailWord_4780439
  simp only [CollatzResearch.WordTrace]
  refine ⟨174356934328293411826680371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116237956218862274551120247 174356934328293411826680371)
  ·
    refine ⟨261535401492440117740020557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174356934328293411826680371 261535401492440117740020557)
    ·
      refine ⟨98075775559665044152507709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 261535401492440117740020557 98075775559665044152507709)
      ·
        refine ⟨36778415834874391557190391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98075775559665044152507709 36778415834874391557190391)
        ·
          refine ⟨55167623752311587335785587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36778415834874391557190391 55167623752311587335785587)
          ·
            refine ⟨82751435628467381003678381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55167623752311587335785587 82751435628467381003678381)
            ·
              refine ⟨31031788360675267876379393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82751435628467381003678381 31031788360675267876379393)
              ·
                refine ⟨23273841270506450907284545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31031788360675267876379393 23273841270506450907284545)
                ·
                  refine ⟨17455380952879838180463409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23273841270506450907284545 17455380952879838180463409)
                  ·
                    refine ⟨13091535714659878635347557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17455380952879838180463409 13091535714659878635347557)
                    ·
                      refine ⟨2454662946498727244127667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13091535714659878635347557 2454662946498727244127667)
                      ·
                        rfl

theorem cell23_4780439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_4780439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780439 prefixEnd_4780439 := by exact prefixLift 4780439
  have htrace : WordTrace (prefixWord ++ tailWord_4780439) baseStart_4780439 baseEnd_4780439 := by
    simpa [prefixWord, tailWord_4780439, baseEnd_4780439] using wordTrace_append hprefix tailTrace_4780439
  have hstable : (prefixWord ++ tailWord_4780439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780439).length < 2 ^ (prefixWord ++ tailWord_4780439).sum := by decide
  have hdescent : baseEnd_4780439 < baseStart_4780439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780500 : List Nat := [2, 4, 1, 2, 2, 2, 3, 2, 5]
def baseStart_4780500 : Nat := 118140960795 + 4780500 * 2 ^ 59
def prefixEnd_4780500 : Nat := 4983230072969 + 3 ^ 40 * 4780500 * 2
def baseEnd_4780500 : Nat := 272743807646516833940543

theorem tailTrace_4780500 : CollatzResearch.WordTrace tailWord_4780500 prefixEnd_4780500 272743807646516833940543 := by
  unfold tailWord_4780500
  simp only [CollatzResearch.WordTrace]
  refine ⟨87179579590536209622325477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116239439454048279496433969 87179579590536209622325477)
  ·
    refine ⟨16346171173225539304186027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87179579590536209622325477 16346171173225539304186027)
    ·
      refine ⟨24519256759838308956279041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16346171173225539304186027 24519256759838308956279041)
      ·
        refine ⟨18389442569878731717209281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24519256759838308956279041 18389442569878731717209281)
        ·
          refine ⟨13792081927409048787906961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18389442569878731717209281 13792081927409048787906961)
          ·
            refine ⟨10344061445556786590930221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13792081927409048787906961 10344061445556786590930221)
            ·
              refine ⟨3879023042083794971598833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10344061445556786590930221 3879023042083794971598833)
              ·
                refine ⟨2909267281562846228699125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3879023042083794971598833 2909267281562846228699125)
                ·
                  refine ⟨272743807646516833940543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2909267281562846228699125 272743807646516833940543)
                  ·
                    rfl

theorem cell23_4780500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_4780500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780500 prefixEnd_4780500 := by exact prefixLift 4780500
  have htrace : WordTrace (prefixWord ++ tailWord_4780500) baseStart_4780500 baseEnd_4780500 := by
    simpa [prefixWord, tailWord_4780500, baseEnd_4780500] using wordTrace_append hprefix tailTrace_4780500
  have hstable : (prefixWord ++ tailWord_4780500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780500).length < 2 ^ (prefixWord ++ tailWord_4780500).sum := by decide
  have hdescent : baseEnd_4780500 < baseStart_4780500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780543 : List Nat := [1, 1, 2, 2, 1, 2, 4, 5, 1, 4]
def baseStart_4780543 : Nat := 118140960795 + 4780543 * 2 ^ 59
def prefixEnd_4780543 : Nat := 4983230072969 + 3 ^ 40 * 4780543 * 2
def baseEnd_4780543 : Nat := 818238782828931612409063

theorem tailTrace_4780543 : CollatzResearch.WordTrace tailWord_4780543 prefixEnd_4780543 818238782828931612409063 := by
  unfold tailWord_4780543
  simp only [CollatzResearch.WordTrace]
  refine ⟨174360727519916637588466283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116240485013277758392310855 174360727519916637588466283)
  ·
    refine ⟨261541091279874956382699425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174360727519916637588466283 261541091279874956382699425)
    ·
      refine ⟨196155818459906217287024569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261541091279874956382699425 196155818459906217287024569)
      ·
        refine ⟨147116863844929662965268427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196155818459906217287024569 147116863844929662965268427)
        ·
          refine ⟨220675295767394494447902641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147116863844929662965268427 220675295767394494447902641)
          ·
            refine ⟨165506471825545870835926981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220675295767394494447902641 165506471825545870835926981)
            ·
              refine ⟨31032463467289850781736309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 165506471825545870835926981 31032463467289850781736309)
              ·
                refine ⟨2909293450058423510787779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31032463467289850781736309 2909293450058423510787779)
                ·
                  refine ⟨4363940175087635266181669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2909293450058423510787779 4363940175087635266181669)
                  ·
                    refine ⟨818238782828931612409063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4363940175087635266181669 818238782828931612409063)
                    ·
                      rfl

theorem cell23_4780543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 5, 1, 4].length) (baseStart_4780543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780543 prefixEnd_4780543 := by exact prefixLift 4780543
  have htrace : WordTrace (prefixWord ++ tailWord_4780543) baseStart_4780543 baseEnd_4780543 := by
    simpa [prefixWord, tailWord_4780543, baseEnd_4780543] using wordTrace_append hprefix tailTrace_4780543
  have hstable : (prefixWord ++ tailWord_4780543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780543).length < 2 ^ (prefixWord ++ tailWord_4780543).sum := by decide
  have hdescent : baseEnd_4780543 < baseStart_4780543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780556 : List Nat := [2, 2, 1, 2, 4, 1, 1, 4, 6]
def baseStart_4780556 : Nat := 118140960795 + 4780556 * 2 ^ 59
def prefixEnd_4780556 : Nat := 4983230072969 + 3 ^ 40 * 4780556 * 2
def baseEnd_4780556 : Nat := 272747002637255920707181

theorem tailTrace_4780556 : CollatzResearch.WordTrace tailWord_4780556 prefixEnd_4780556 272747002637255920707181 := by
  unfold tailWord_4780556
  simp only [CollatzResearch.WordTrace]
  refine ⟨87180600834434770404344761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116240801112579693872459681 87180600834434770404344761)
  ·
    refine ⟨65385450625826077803258571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87180600834434770404344761 65385450625826077803258571)
    ·
      refine ⟨98078175938739116704887857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65385450625826077803258571 98078175938739116704887857)
      ·
        refine ⟨73558631954054337528665893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98078175938739116704887857 73558631954054337528665893)
        ·
          refine ⟨13792243491385188286624855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73558631954054337528665893 13792243491385188286624855)
          ·
            refine ⟨20688365237077782429937283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13792243491385188286624855 20688365237077782429937283)
            ·
              refine ⟨31032547855616673644905925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20688365237077782429937283 31032547855616673644905925)
              ·
                refine ⟨5818602722928126308419861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31032547855616673644905925 5818602722928126308419861)
                ·
                  refine ⟨272747002637255920707181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5818602722928126308419861 272747002637255920707181)
                  ·
                    rfl

theorem cell23_4780556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4, 6].length) (baseStart_4780556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780556 prefixEnd_4780556 := by exact prefixLift 4780556
  have htrace : WordTrace (prefixWord ++ tailWord_4780556) baseStart_4780556 baseEnd_4780556 := by
    simpa [prefixWord, tailWord_4780556, baseEnd_4780556] using wordTrace_append hprefix tailTrace_4780556
  have hstable : (prefixWord ++ tailWord_4780556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780556).length < 2 ^ (prefixWord ++ tailWord_4780556).sum := by decide
  have hdescent : baseEnd_4780556 < baseStart_4780556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780640 : List Nat := [2, 1, 1, 3, 2, 1, 4, 2, 3, 2, 2]
def baseStart_4780640 : Nat := 118140960795 + 4780640 * 2 ^ 59
def prefixEnd_4780640 : Nat := 4983230072969 + 3 ^ 40 * 4780640 * 2
def baseEnd_4780640 : Nat := 2454766156110280957714243

theorem tailTrace_4780640 : CollatzResearch.WordTrace tailWord_4780640 prefixEnd_4780640 2454766156110280957714243 := by
  unfold tailWord_4780640
  simp only [CollatzResearch.WordTrace]
  refine ⟨87182132700282611577373687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116242843600376815436498249 87182132700282611577373687)
  ·
    refine ⟨130773199050423917366060531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87182132700282611577373687 130773199050423917366060531)
    ·
      refine ⟨196159798575635876049090797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130773199050423917366060531 196159798575635876049090797)
      ·
        refine ⟨73559924465863453518409049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196159798575635876049090797 73559924465863453518409049)
        ·
          refine ⟨55169943349397590138806787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73559924465863453518409049 55169943349397590138806787)
          ·
            refine ⟨82754915024096385208210181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55169943349397590138806787 82754915024096385208210181)
            ·
              refine ⟨15516546567018072226539409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82754915024096385208210181 15516546567018072226539409)
              ·
                refine ⟨11637409925263554169904557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15516546567018072226539409 11637409925263554169904557)
                ·
                  refine ⟨4364028721973832813714209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11637409925263554169904557 4364028721973832813714209)
                  ·
                    refine ⟨3273021541480374610285657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4364028721973832813714209 3273021541480374610285657)
                    ·
                      refine ⟨2454766156110280957714243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3273021541480374610285657 2454766156110280957714243)
                      ·
                        rfl

theorem cell23_4780640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 3, 2, 2].length) (baseStart_4780640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780640 prefixEnd_4780640 := by exact prefixLift 4780640
  have htrace : WordTrace (prefixWord ++ tailWord_4780640) baseStart_4780640 baseEnd_4780640 := by
    simpa [prefixWord, tailWord_4780640, baseEnd_4780640] using wordTrace_append hprefix tailTrace_4780640
  have hstable : (prefixWord ++ tailWord_4780640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780640).length < 2 ^ (prefixWord ++ tailWord_4780640).sum := by decide
  have hdescent : baseEnd_4780640 < baseStart_4780640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780713 : List Nat := [1, 2, 1, 1, 1, 1, 2, 5, 3, 4, 2]
def baseStart_4780713 : Nat := 118140960795 + 4780713 * 2 ^ 59
def prefixEnd_4780713 : Nat := 4983230072969 + 3 ^ 40 * 4780713 * 2
def baseEnd_4780713 : Nat := 2454803640198059172101407

theorem tailTrace_4780713 : CollatzResearch.WordTrace tailWord_4780713 prefixEnd_4780713 2454803640198059172101407 := by
  unfold tailWord_4780713
  simp only [CollatzResearch.WordTrace]
  refine ⟨174366927929300756622154793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116244618619533837748103195 174366927929300756622154793)
  ·
    refine ⟨130775195946975567466616095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174366927929300756622154793 130775195946975567466616095)
    ·
      refine ⟨196162793920463351199924143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130775195946975567466616095 196162793920463351199924143)
      ·
        refine ⟨294244190880695026799886215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196162793920463351199924143 294244190880695026799886215)
        ·
          refine ⟨441366286321042540199829323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294244190880695026799886215 441366286321042540199829323)
          ·
            refine ⟨662049429481563810299743985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 441366286321042540199829323 662049429481563810299743985)
            ·
              refine ⟨496537072111172857724807989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 662049429481563810299743985 496537072111172857724807989)
              ·
                refine ⟨46550350510422455411700749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 496537072111172857724807989 46550350510422455411700749)
                ·
                  refine ⟨17456381441408420779387781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46550350510422455411700749 17456381441408420779387781)
                  ·
                    refine ⟨3273071520264078896135209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17456381441408420779387781 3273071520264078896135209)
                    ·
                      refine ⟨2454803640198059172101407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3273071520264078896135209 2454803640198059172101407)
                      ·
                        rfl

theorem cell23_4780713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 4, 2].length) (baseStart_4780713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780713 prefixEnd_4780713 := by exact prefixLift 4780713
  have htrace : WordTrace (prefixWord ++ tailWord_4780713) baseStart_4780713 baseEnd_4780713 := by
    simpa [prefixWord, tailWord_4780713, baseEnd_4780713] using wordTrace_append hprefix tailTrace_4780713
  have hstable : (prefixWord ++ tailWord_4780713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780713).length < 2 ^ (prefixWord ++ tailWord_4780713).sum := by decide
  have hdescent : baseEnd_4780713 < baseStart_4780713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780733 : List Nat := [1, 4, 1, 2, 1, 3, 1, 1, 2, 4, 3]
def baseStart_4780733 : Nat := 118140960795 + 4780733 * 2 ^ 59
def prefixEnd_4780733 : Nat := 4983230072969 + 3 ^ 40 * 4780733 * 2
def baseEnd_4780733 : Nat := 2454813909811149093851315

theorem tailTrace_4780733 : CollatzResearch.WordTrace tailWord_4780733 prefixEnd_4780733 2454813909811149093851315 := by
  unfold tailWord_4780733
  simp only [CollatzResearch.WordTrace]
  refine ⟨174367657389228300037882853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116245104926152200025255235 174367657389228300037882853)
  ·
    refine ⟨32693935760480306257103035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174367657389228300037882853 32693935760480306257103035)
    ·
      refine ⟨49040903640720459385654553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32693935760480306257103035 49040903640720459385654553)
      ·
        refine ⟨36780677730540344539240915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49040903640720459385654553 36780677730540344539240915)
        ·
          refine ⟨55171016595810516808861373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36780677730540344539240915 55171016595810516808861373)
          ·
            refine ⟨20689131223428943803323015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55171016595810516808861373 20689131223428943803323015)
            ·
              refine ⟨31033696835143415704984523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20689131223428943803323015 31033696835143415704984523)
              ·
                refine ⟨46550545252715123557476785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31033696835143415704984523 46550545252715123557476785)
                ·
                  refine ⟨34912908939536342668107589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46550545252715123557476785 34912908939536342668107589)
                  ·
                    refine ⟨6546170426163064250270173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34912908939536342668107589 6546170426163064250270173)
                    ·
                      refine ⟨2454813909811149093851315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6546170426163064250270173 2454813909811149093851315)
                      ·
                        rfl

theorem cell23_4780733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_4780733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780733 prefixEnd_4780733 := by exact prefixLift 4780733
  have htrace : WordTrace (prefixWord ++ tailWord_4780733) baseStart_4780733 baseEnd_4780733 := by
    simpa [prefixWord, tailWord_4780733, baseEnd_4780733] using wordTrace_append hprefix tailTrace_4780733
  have hstable : (prefixWord ++ tailWord_4780733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780733).length < 2 ^ (prefixWord ++ tailWord_4780733).sum := by decide
  have hdescent : baseEnd_4780733 < baseStart_4780733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780880 : List Nat := [2, 1, 1, 1, 1, 4, 2, 3, 1, 5, 2]
def baseStart_4780880 : Nat := 118140960795 + 4780880 * 2 ^ 59
def prefixEnd_4780880 : Nat := 4983230072969 + 3 ^ 40 * 4780880 * 2
def baseEnd_4780880 : Nat := 2454889391467360018713139

theorem tailTrace_4780880 : CollatzResearch.WordTrace tailWord_4780880 prefixEnd_4780880 2454889391467360018713139 := by
  unfold tailWord_4780880
  simp only [CollatzResearch.WordTrace]
  refine ⟨87186509459847872071742047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116248679279797162762322729 87186509459847872071742047)
  ·
    refine ⟨130779764189771808107613071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87186509459847872071742047 130779764189771808107613071)
    ·
      refine ⟨196169646284657712161419607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130779764189771808107613071 196169646284657712161419607)
      ·
        refine ⟨294254469426986568242129411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196169646284657712161419607 294254469426986568242129411)
        ·
          refine ⟨441381704140479852363194117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294254469426986568242129411 441381704140479852363194117)
          ·
            refine ⟨82759069526339972318098897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 441381704140479852363194117 82759069526339972318098897)
            ·
              refine ⟨62069302144754979238574173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82759069526339972318098897 62069302144754979238574173)
              ·
                refine ⟨23275988304283117214465315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62069302144754979238574173 23275988304283117214465315)
                ·
                  refine ⟨34913982456424675821697973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23275988304283117214465315 34913982456424675821697973)
                  ·
                    refine ⟨3273185855289813358284185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34913982456424675821697973 3273185855289813358284185)
                    ·
                      refine ⟨2454889391467360018713139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3273185855289813358284185 2454889391467360018713139)
                      ·
                        rfl

theorem cell23_4780880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 1, 5, 2].length) (baseStart_4780880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780880 prefixEnd_4780880 := by exact prefixLift 4780880
  have htrace : WordTrace (prefixWord ++ tailWord_4780880) baseStart_4780880 baseEnd_4780880 := by
    simpa [prefixWord, tailWord_4780880, baseEnd_4780880] using wordTrace_append hprefix tailTrace_4780880
  have hstable : (prefixWord ++ tailWord_4780880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780880).length < 2 ^ (prefixWord ++ tailWord_4780880).sum := by decide
  have hdescent : baseEnd_4780880 < baseStart_4780880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780898 : List Nat := [3, 3, 2, 1, 3, 2, 2, 2, 1, 4]
def baseStart_4780898 : Nat := 118140960795 + 4780898 * 2 ^ 59
def prefixEnd_4780898 : Nat := 4983230072969 + 3 ^ 40 * 4780898 * 2
def baseEnd_4780898 : Nat := 818299544706380316096019

theorem tailTrace_4780898 : CollatzResearch.WordTrace tailWord_4780898 prefixEnd_4780898 818299544706380316096019 := by
  unfold tailWord_4780898
  simp only [CollatzResearch.WordTrace]
  refine ⟨43593418858407633304409837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116249116955753688811759565 43593418858407633304409837)
  ·
    refine ⟨16347532071902862489153689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43593418858407633304409837 16347532071902862489153689)
    ·
      refine ⟨12260649053927146866865267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16347532071902862489153689 12260649053927146866865267)
      ·
        refine ⟨18390973580890720300297901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12260649053927146866865267 18390973580890720300297901)
        ·
          refine ⟨6896615092834020112611713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18390973580890720300297901 6896615092834020112611713)
          ·
            refine ⟨5172461319625515084458785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6896615092834020112611713 5172461319625515084458785)
            ·
              refine ⟨3879345989719136313344089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5172461319625515084458785 3879345989719136313344089)
              ·
                refine ⟨2909509492289352235008067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3879345989719136313344089 2909509492289352235008067)
                ·
                  refine ⟨4364264238434028352512101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2909509492289352235008067 4364264238434028352512101)
                  ·
                    refine ⟨818299544706380316096019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4364264238434028352512101 818299544706380316096019)
                    ·
                      rfl

theorem cell23_4780898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_4780898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780898 prefixEnd_4780898 := by exact prefixLift 4780898
  have htrace : WordTrace (prefixWord ++ tailWord_4780898) baseStart_4780898 baseEnd_4780898 := by
    simpa [prefixWord, tailWord_4780898, baseEnd_4780898] using wordTrace_append hprefix tailTrace_4780898
  have hstable : (prefixWord ++ tailWord_4780898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780898).length < 2 ^ (prefixWord ++ tailWord_4780898).sum := by decide
  have hdescent : baseEnd_4780898 < baseStart_4780898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780923 : List Nat := [1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 6]
def baseStart_4780923 : Nat := 118140960795 + 4780923 * 2 ^ 59
def prefixEnd_4780923 : Nat := 4983230072969 + 3 ^ 40 * 4780923 * 2
def baseEnd_4780923 : Nat := 2454911471135503350475441

theorem tailTrace_4780923 : CollatzResearch.WordTrace tailWord_4780923 prefixEnd_4780923 2454911471135503350475441 := by
  unfold tailWord_4780923
  simp only [CollatzResearch.WordTrace]
  refine ⟨174374587258539962487299423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116249724839026641658199615 174374587258539962487299423)
  ·
    refine ⟨261561880887809943730949135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174374587258539962487299423 261561880887809943730949135)
    ·
      refine ⟨392342821331714915596423703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261561880887809943730949135 392342821331714915596423703)
      ·
        refine ⟨588514231997572373394635555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 392342821331714915596423703 588514231997572373394635555)
        ·
          refine ⟨882771347996358560091953333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 588514231997572373394635555 882771347996358560091953333)
          ·
            refine ⟨82759813874658615008620625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 882771347996358560091953333 82759813874658615008620625)
            ·
              refine ⟨62069860405993961256465469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82759813874658615008620625 62069860405993961256465469)
              ·
                refine ⟨23276197652247735471174551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62069860405993961256465469 23276197652247735471174551)
                ·
                  refine ⟨34914296478371603206761827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23276197652247735471174551 34914296478371603206761827)
                  ·
                    refine ⟨52371444717557404810142741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34914296478371603206761827 52371444717557404810142741)
                    ·
                      refine ⟨2454911471135503350475441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52371444717557404810142741 2454911471135503350475441)
                      ·
                        rfl

theorem cell23_4780923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 6].length) (baseStart_4780923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780923 prefixEnd_4780923 := by exact prefixLift 4780923
  have htrace : WordTrace (prefixWord ++ tailWord_4780923) baseStart_4780923 baseEnd_4780923 := by
    simpa [prefixWord, tailWord_4780923, baseEnd_4780923] using wordTrace_append hprefix tailTrace_4780923
  have hstable : (prefixWord ++ tailWord_4780923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780923).length < 2 ^ (prefixWord ++ tailWord_4780923).sum := by decide
  have hdescent : baseEnd_4780923 < baseStart_4780923 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780927 : List Nat := [1, 1, 2, 2, 1, 1, 5, 1, 5, 2, 2]
def baseStart_4780927 : Nat := 118140960795 + 4780927 * 2 ^ 59
def prefixEnd_4780927 : Nat := 4983230072969 + 3 ^ 40 * 4780927 * 2
def baseEnd_4780927 : Nat := 2454913525058121334825423

theorem tailTrace_4780927 : CollatzResearch.WordTrace tailWord_4780927 prefixEnd_4780927 2454913525058121334825423 := by
  unfold tailWord_4780927
  simp only [CollatzResearch.WordTrace]
  refine ⟨174374733150525471170445035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116249822100350314113630023 174374733150525471170445035)
  ·
    refine ⟨261562099725788206755667553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174374733150525471170445035 261562099725788206755667553)
    ·
      refine ⟨196171574794341155066750665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261562099725788206755667553 196171574794341155066750665)
      ·
        refine ⟨147128681095755866300062999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196171574794341155066750665 147128681095755866300062999)
        ·
          refine ⟨220693021643633799450094499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147128681095755866300062999 220693021643633799450094499)
          ·
            refine ⟨331039532465450699175141749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220693021643633799450094499 331039532465450699175141749)
            ·
              refine ⟨31034956168636003047669539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 331039532465450699175141749 31034956168636003047669539)
              ·
                refine ⟨46552434252954004571504309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31034956168636003047669539 46552434252954004571504309)
                ·
                  refine ⟨4364290711214437928578529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46552434252954004571504309 4364290711214437928578529)
                  ·
                    refine ⟨3273218033410828446433897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4364290711214437928578529 3273218033410828446433897)
                    ·
                      refine ⟨2454913525058121334825423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3273218033410828446433897 2454913525058121334825423)
                      ·
                        rfl

theorem cell23_4780927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 5, 2, 2].length) (baseStart_4780927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780927 prefixEnd_4780927 := by exact prefixLift 4780927
  have htrace : WordTrace (prefixWord ++ tailWord_4780927) baseStart_4780927 baseEnd_4780927 := by
    simpa [prefixWord, tailWord_4780927, baseEnd_4780927] using wordTrace_append hprefix tailTrace_4780927
  have hstable : (prefixWord ++ tailWord_4780927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780927).length < 2 ^ (prefixWord ++ tailWord_4780927).sum := by decide
  have hdescent : baseEnd_4780927 < baseStart_4780927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780940 : List Nat := [2, 2, 1, 2, 1, 2, 4, 2, 1, 2, 4]
def baseStart_4780940 : Nat := 118140960795 + 4780940 * 2 ^ 59
def prefixEnd_4780940 : Nat := 4983230072969 + 3 ^ 40 * 4780940 * 2
def baseEnd_4780940 : Nat := 2454920200306629783962863

theorem tailTrace_4780940 : CollatzResearch.WordTrace tailWord_4780940 prefixEnd_4780940 2454920200306629783962863 := by
  unfold tailWord_4780940
  simp only [CollatzResearch.WordTrace]
  refine ⟨87187603649739187195334137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116250138199652249593778849 87187603649739187195334137)
  ·
    refine ⟨65390702737304390396500603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87187603649739187195334137 65390702737304390396500603)
    ·
      refine ⟨98086054105956585594750905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65390702737304390396500603 98086054105956585594750905)
      ·
        refine ⟨73564540579467439196063179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98086054105956585594750905 73564540579467439196063179)
        ·
          refine ⟨110346810869201158794094769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73564540579467439196063179 110346810869201158794094769)
          ·
            refine ⟨82760108151900869095571077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110346810869201158794094769 82760108151900869095571077)
            ·
              refine ⟨15517520278481412955419577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82760108151900869095571077 15517520278481412955419577)
              ·
                refine ⟨11638140208861059716564683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15517520278481412955419577 11638140208861059716564683)
                ·
                  refine ⟨17457210313291589574847025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11638140208861059716564683 17457210313291589574847025)
                  ·
                    refine ⟨13092907734968692181135269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17457210313291589574847025 13092907734968692181135269)
                    ·
                      refine ⟨2454920200306629783962863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13092907734968692181135269 2454920200306629783962863)
                      ·
                        rfl

theorem cell23_4780940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_4780940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780940 prefixEnd_4780940 := by exact prefixLift 4780940
  have htrace : WordTrace (prefixWord ++ tailWord_4780940) baseStart_4780940 baseEnd_4780940 := by
    simpa [prefixWord, tailWord_4780940, baseEnd_4780940] using wordTrace_append hprefix tailTrace_4780940
  have hstable : (prefixWord ++ tailWord_4780940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780940).length < 2 ^ (prefixWord ++ tailWord_4780940).sum := by decide
  have hdescent : baseEnd_4780940 < baseStart_4780940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780953 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 2, 2, 6]
def baseStart_4780953 : Nat := 118140960795 + 4780953 * 2 ^ 59
def prefixEnd_4780953 : Nat := 4983230072969 + 3 ^ 40 * 4780953 * 2
def baseEnd_4780953 : Nat := 2454926875555138233100303

theorem tailTrace_4780953 : CollatzResearch.WordTrace tailWord_4780953 prefixEnd_4780953 2454926875555138233100303 := by
  unfold tailWord_4780953
  simp only [CollatzResearch.WordTrace]
  refine ⟨174375681448431277610891513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116250454298954185073927675 174375681448431277610891513)
  ·
    refine ⟨130781761086323458208168635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174375681448431277610891513 130781761086323458208168635)
    ·
      refine ⟨196172641629485187312252953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130781761086323458208168635 196172641629485187312252953)
      ·
        refine ⟨147129481222113890484189715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196172641629485187312252953 147129481222113890484189715)
        ·
          refine ⟨220694221833170835726284573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147129481222113890484189715 220694221833170835726284573)
          ·
            refine ⟨82760333187439063397356715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 220694221833170835726284573 82760333187439063397356715)
            ·
              refine ⟨124140499781158595096035073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82760333187439063397356715 124140499781158595096035073)
              ·
                refine ⟨93105374835868946322026305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124140499781158595096035073 93105374835868946322026305)
                ·
                  refine ⟨69829031126901709741519729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93105374835868946322026305 69829031126901709741519729)
                  ·
                    refine ⟨52371773345176282306139797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 69829031126901709741519729 52371773345176282306139797)
                    ·
                      refine ⟨2454926875555138233100303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52371773345176282306139797 2454926875555138233100303)
                      ·
                        rfl

theorem cell23_4780953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_4780953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780953 prefixEnd_4780953 := by exact prefixLift 4780953
  have htrace : WordTrace (prefixWord ++ tailWord_4780953) baseStart_4780953 baseEnd_4780953 := by
    simpa [prefixWord, tailWord_4780953, baseEnd_4780953] using wordTrace_append hprefix tailTrace_4780953
  have hstable : (prefixWord ++ tailWord_4780953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780953).length < 2 ^ (prefixWord ++ tailWord_4780953).sum := by decide
  have hdescent : baseEnd_4780953 < baseStart_4780953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780960 : List Nat := [2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 3]
def baseStart_4780960 : Nat := 118140960795 + 4780960 * 2 ^ 59
def prefixEnd_4780960 : Nat := 4983230072969 + 3 ^ 40 * 4780960 * 2
def baseEnd_4780960 : Nat := 2454930469919719705712771

theorem tailTrace_4780960 : CollatzResearch.WordTrace tailWord_4780960 prefixEnd_4780960 2454930469919719705712771 := by
  unfold tailWord_4780960
  simp only [CollatzResearch.WordTrace]
  refine ⟨87187968379702958903198167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116250624506270611870930889 87187968379702958903198167)
  ·
    refine ⟨130781952569554438354797251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87187968379702958903198167 130781952569554438354797251)
    ·
      refine ⟨196172928854331657532195877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130781952569554438354797251 196172928854331657532195877)
      ·
        refine ⟨36782424160187185787286727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 196172928854331657532195877 36782424160187185787286727)
        ·
          refine ⟨55173636240280778680930091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36782424160187185787286727 55173636240280778680930091)
          ·
            refine ⟨82760454360421168021395137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55173636240280778680930091 82760454360421168021395137)
            ·
              refine ⟨62070340770315876016046353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82760454360421168021395137 62070340770315876016046353)
              ·
                refine ⟨46552755577736907012034765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62070340770315876016046353 46552755577736907012034765)
                ·
                  refine ⟨17457283341651340129513037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46552755577736907012034765 17457283341651340129513037)
                  ·
                    refine ⟨6546481253119252548567389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17457283341651340129513037 6546481253119252548567389)
                    ·
                      refine ⟨2454930469919719705712771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6546481253119252548567389 2454930469919719705712771)
                      ·
                        rfl

theorem cell23_4780960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_4780960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780960 prefixEnd_4780960 := by exact prefixLift 4780960
  have htrace : WordTrace (prefixWord ++ tailWord_4780960) baseStart_4780960 baseEnd_4780960 := by
    simpa [prefixWord, tailWord_4780960, baseEnd_4780960] using wordTrace_append hprefix tailTrace_4780960
  have hstable : (prefixWord ++ tailWord_4780960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780960).length < 2 ^ (prefixWord ++ tailWord_4780960).sum := by decide
  have hdescent : baseEnd_4780960 < baseStart_4780960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780961 : List Nat := [1, 2, 3, 4, 1, 2, 2, 1, 3, 2, 2]
def baseStart_4780961 : Nat := 118140960795 + 4780961 * 2 ^ 59
def prefixEnd_4780961 : Nat := 4983230072969 + 3 ^ 40 * 4780961 * 2
def baseEnd_4780961 : Nat := 2454930983400374201800267

theorem tailTrace_4780961 : CollatzResearch.WordTrace tailWord_4780961 prefixEnd_4780961 2454930983400374201800267 := by
  unfold tailWord_4780961
  simp only [CollatzResearch.WordTrace]
  refine ⟨174375973232402294977182737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116250648821601529984788491 174375973232402294977182737)
  ·
    refine ⟨130781979924301721232887053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174375973232402294977182737 130781979924301721232887053)
    ·
      refine ⟨49043242471613145462332645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130781979924301721232887053 49043242471613145462332645)
      ·
        refine ⟨9195607963427464774187371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49043242471613145462332645 9195607963427464774187371)
        ·
          refine ⟨13793411945141197161281057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9195607963427464774187371 13793411945141197161281057)
          ·
            refine ⟨10345058958855897870960793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13793411945141197161281057 10345058958855897870960793)
            ·
              refine ⟨7758794219141923403220595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10345058958855897870960793 7758794219141923403220595)
              ·
                refine ⟨11638191328712885104830893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7758794219141923403220595 11638191328712885104830893)
                ·
                  refine ⟨4364321748267331914311585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11638191328712885104830893 4364321748267331914311585)
                  ·
                    refine ⟨3273241311200498935733689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4364321748267331914311585 3273241311200498935733689)
                    ·
                      refine ⟨2454930983400374201800267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3273241311200498935733689 2454930983400374201800267)
                      ·
                        rfl

theorem cell23_4780961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_4780961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780961 prefixEnd_4780961 := by exact prefixLift 4780961
  have htrace : WordTrace (prefixWord ++ tailWord_4780961) baseStart_4780961 baseEnd_4780961 := by
    simpa [prefixWord, tailWord_4780961, baseEnd_4780961] using wordTrace_append hprefix tailTrace_4780961
  have hstable : (prefixWord ++ tailWord_4780961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780961).length < 2 ^ (prefixWord ++ tailWord_4780961).sum := by decide
  have hdescent : baseEnd_4780961 < baseStart_4780961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780963 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 1, 9]
def baseStart_4780963 : Nat := 118140960795 + 4780963 * 2 ^ 59
def prefixEnd_4780963 : Nat := 4983230072969 + 3 ^ 40 * 4780963 * 2
def baseEnd_4780963 : Nat := 818310670120561064658419

theorem tailTrace_4780963 : CollatzResearch.WordTrace tailWord_4780963 prefixEnd_4780963 818310670120561064658419 := by
  unfold tailWord_4780963
  simp only [CollatzResearch.WordTrace]
  refine ⟨174376046178395049318755543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116250697452263366212503695 174376046178395049318755543)
  ·
    refine ⟨261564069267592573978133315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174376046178395049318755543 261564069267592573978133315)
    ·
      refine ⟨392346103901388860967199973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261564069267592573978133315 392346103901388860967199973)
      ·
        refine ⟨73564894481510411431349995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 392346103901388860967199973 73564894481510411431349995)
        ·
          refine ⟨110347341722265617147024993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73564894481510411431349995 110347341722265617147024993)
          ·
            refine ⟨82760506291699212860268745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110347341722265617147024993 82760506291699212860268745)
            ·
              refine ⟨62070379718774409645201559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82760506291699212860268745 62070379718774409645201559)
              ·
                refine ⟨93105569578161614467802339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62070379718774409645201559 93105569578161614467802339)
                ·
                  refine ⟨139658354367242421701703509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93105569578161614467802339 139658354367242421701703509)
                  ·
                    refine ⟨818310670120561064658419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 139658354367242421701703509 818310670120561064658419)
                    ·
                      rfl

theorem cell23_4780963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 9].length) (baseStart_4780963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780963 prefixEnd_4780963 := by exact prefixLift 4780963
  have htrace : WordTrace (prefixWord ++ tailWord_4780963) baseStart_4780963 baseEnd_4780963 := by
    simpa [prefixWord, tailWord_4780963, baseEnd_4780963] using wordTrace_append hprefix tailTrace_4780963
  have hstable : (prefixWord ++ tailWord_4780963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780963).length < 2 ^ (prefixWord ++ tailWord_4780963).sum := by decide
  have hdescent : baseEnd_4780963 < baseStart_4780963 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4780990 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5]
def baseStart_4780990 : Nat := 118140960795 + 4780990 * 2 ^ 59
def prefixEnd_4780990 : Nat := 4983230072969 + 3 ^ 40 * 4780990 * 2
def baseEnd_4780990 : Nat := 2454945874339354588337633

theorem tailTrace_4780990 : CollatzResearch.WordTrace tailWord_4780990 prefixEnd_4780990 2454945874339354588337633 := by
  unfold tailWord_4780990
  simp only [CollatzResearch.WordTrace]
  refine ⟨21797128868662154116248553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116251353966198155286658949 21797128868662154116248553)
  ·
    refine ⟨16347846651496615587186415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21797128868662154116248553 16347846651496615587186415)
    ·
      refine ⟨24521769977244923380779623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16347846651496615587186415 24521769977244923380779623)
      ·
        refine ⟨36782654965867385071169435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24521769977244923380779623 36782654965867385071169435)
        ·
          refine ⟨55173982448801077606754153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36782654965867385071169435 55173982448801077606754153)
          ·
            refine ⟨41380486836600808205065615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55173982448801077606754153 41380486836600808205065615)
            ·
              refine ⟨62070730254901212307598423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41380486836600808205065615 62070730254901212307598423)
              ·
                refine ⟨93106095382351818461397635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62070730254901212307598423 93106095382351818461397635)
                ·
                  refine ⟨139659143073527727692096453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93106095382351818461397635 139659143073527727692096453)
                  ·
                    refine ⟨26186089326286448942268085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 139659143073527727692096453 26186089326286448942268085)
                    ·
                      refine ⟨2454945874339354588337633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26186089326286448942268085 2454945874339354588337633)
                      ·
                        rfl

theorem cell23_4780990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_4780990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4780990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4780990 prefixEnd_4780990 := by exact prefixLift 4780990
  have htrace : WordTrace (prefixWord ++ tailWord_4780990) baseStart_4780990 baseEnd_4780990 := by
    simpa [prefixWord, tailWord_4780990, baseEnd_4780990] using wordTrace_append hprefix tailTrace_4780990
  have hstable : (prefixWord ++ tailWord_4780990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4780990).length < 2 ^ (prefixWord ++ tailWord_4780990).sum := by decide
  have hdescent : baseEnd_4780990 < baseStart_4780990 := by decide
  rcases family_descends (prefixWord ++ tailWord_4780990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781004 : List Nat := [2, 2, 1, 4, 1, 1, 1, 5, 1, 3, 2]
def baseStart_4781004 : Nat := 118140960795 + 4781004 * 2 ^ 59
def prefixEnd_4781004 : Nat := 4983230072969 + 3 ^ 40 * 4781004 * 2
def baseEnd_4781004 : Nat := 2454953063068517533562569

theorem tailTrace_4781004 : CollatzResearch.WordTrace tailWord_4781004 prefixEnd_4781004 2454953063068517533562569 := by
  unfold tailWord_4781004
  simp only [CollatzResearch.WordTrace]
  refine ⟨87188770785623256660499033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116251694380831008880665377 87188770785623256660499033)
  ·
    refine ⟨65391578089217442495374275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87188770785623256660499033 65391578089217442495374275)
    ·
      refine ⟨98087367133826163743061413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65391578089217442495374275 98087367133826163743061413)
      ·
        refine ⟨18391381337592405701824015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98087367133826163743061413 18391381337592405701824015)
        ·
          refine ⟨27587072006388608552736023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18391381337592405701824015 27587072006388608552736023)
          ·
            refine ⟨41380608009582912829104035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27587072006388608552736023 41380608009582912829104035)
            ·
              refine ⟨62070912014374369243656053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41380608009582912829104035 62070912014374369243656053)
              ·
                refine ⟨5819148001347597116592755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62070912014374369243656053 5819148001347597116592755)
                ·
                  refine ⟨8728722002021395674889133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5819148001347597116592755 8728722002021395674889133)
                  ·
                    refine ⟨3273270750758023378083425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8728722002021395674889133 3273270750758023378083425)
                    ·
                      refine ⟨2454953063068517533562569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3273270750758023378083425 2454953063068517533562569)
                      ·
                        rfl

theorem cell23_4781004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_4781004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781004 prefixEnd_4781004 := by exact prefixLift 4781004
  have htrace : WordTrace (prefixWord ++ tailWord_4781004) baseStart_4781004 baseEnd_4781004 := by
    simpa [prefixWord, tailWord_4781004, baseEnd_4781004] using wordTrace_append hprefix tailTrace_4781004
  have hstable : (prefixWord ++ tailWord_4781004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781004).length < 2 ^ (prefixWord ++ tailWord_4781004).sum := by decide
  have hdescent : baseEnd_4781004 < baseStart_4781004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781038 : List Nat := [4, 1, 2, 1, 4, 2, 1, 2, 1, 3, 2]
def baseStart_4781038 : Nat := 118140960795 + 4781038 * 2 ^ 59
def prefixEnd_4781038 : Nat := 4983230072969 + 3 ^ 40 * 4781038 * 2
def baseEnd_4781038 : Nat := 2454970521410770400537413

theorem tailTrace_4781038 : CollatzResearch.WordTrace tailWord_4781038 prefixEnd_4781038 2454970521410770400537413 := by
  unfold tailWord_4781038
  simp only [CollatzResearch.WordTrace]
  refine ⟨21797347706640417140966971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116252521102082224751823845 21797347706640417140966971)
  ·
    refine ⟨32696021559960625711450457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21797347706640417140966971 32696021559960625711450457)
    ·
      refine ⟨24522016169970469283587843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32696021559960625711450457 24522016169970469283587843)
      ·
        refine ⟨36783024254955703925381765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24522016169970469283587843 36783024254955703925381765)
        ·
          refine ⟨6896817047804194486009081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36783024254955703925381765 6896817047804194486009081)
          ·
            refine ⟨5172612785853145864506811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6896817047804194486009081 5172612785853145864506811)
            ·
              refine ⟨7758919178779718796760217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5172612785853145864506811 7758919178779718796760217)
              ·
                refine ⟨5819189384084789097570163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7758919178779718796760217 5819189384084789097570163)
                ·
                  refine ⟨8728784076127183646355245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5819189384084789097570163 8728784076127183646355245)
                  ·
                    refine ⟨3273294028547693867383217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8728784076127183646355245 3273294028547693867383217)
                    ·
                      refine ⟨2454970521410770400537413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3273294028547693867383217 2454970521410770400537413)
                      ·
                        rfl

theorem cell23_4781038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 2, 1, 3, 2].length) (baseStart_4781038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781038 prefixEnd_4781038 := by exact prefixLift 4781038
  have htrace : WordTrace (prefixWord ++ tailWord_4781038) baseStart_4781038 baseEnd_4781038 := by
    simpa [prefixWord, tailWord_4781038, baseEnd_4781038] using wordTrace_append hprefix tailTrace_4781038
  have hstable : (prefixWord ++ tailWord_4781038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781038).length < 2 ^ (prefixWord ++ tailWord_4781038).sum := by decide
  have hdescent : baseEnd_4781038 < baseStart_4781038 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781084 : List Nat := [2, 2, 3, 1, 4, 1, 1, 1, 2, 3, 3]
def baseStart_4781084 : Nat := 118140960795 + 4781084 * 2 ^ 59
def prefixEnd_4781084 : Nat := 4983230072969 + 3 ^ 40 * 4781084 * 2
def baseEnd_4781084 : Nat := 2454994141520877220562201

theorem tailTrace_4781084 : CollatzResearch.WordTrace tailWord_4781084 prefixEnd_4781084 2454994141520877220562201 := by
  unfold tailWord_4781084
  simp only [CollatzResearch.WordTrace]
  refine ⟨87190229705478343491955153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116253639607304457989273537 87190229705478343491955153)
  ·
    refine ⟨65392672279108757618966365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87190229705478343491955153 65392672279108757618966365)
    ·
      refine ⟨24522252104665784107112387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65392672279108757618966365 24522252104665784107112387)
      ·
        refine ⟨36783378156998676160668581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24522252104665784107112387 36783378156998676160668581)
        ·
          refine ⟨6896883404437251780125359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36783378156998676160668581 6896883404437251780125359)
          ·
            refine ⟨10345325106655877670188039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6896883404437251780125359 10345325106655877670188039)
            ·
              refine ⟨15517987659983816505282059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10345325106655877670188039 15517987659983816505282059)
              ·
                refine ⟨23276981489975724757923089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15517987659983816505282059 23276981489975724757923089)
                ·
                  refine ⟨17457736117481793568442317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23276981489975724757923089 17457736117481793568442317)
                  ·
                    refine ⟨6546651044055672588165869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17457736117481793568442317 6546651044055672588165869)
                    ·
                      refine ⟨2454994141520877220562201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6546651044055672588165869 2454994141520877220562201)
                      ·
                        rfl

theorem cell23_4781084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_4781084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781084 prefixEnd_4781084 := by exact prefixLift 4781084
  have htrace : WordTrace (prefixWord ++ tailWord_4781084) baseStart_4781084 baseEnd_4781084 := by
    simpa [prefixWord, tailWord_4781084, baseEnd_4781084] using wordTrace_append hprefix tailTrace_4781084
  have hstable : (prefixWord ++ tailWord_4781084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781084).length < 2 ^ (prefixWord ++ tailWord_4781084).sum := by decide
  have hdescent : baseEnd_4781084 < baseStart_4781084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781107 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 3, 6, 2]
def baseStart_4781107 : Nat := 118140960795 + 4781107 * 2 ^ 59
def prefixEnd_4781107 : Nat := 4983230072969 + 3 ^ 40 * 4781107 * 2
def baseEnd_4781107 : Nat := 2455005951575930630574595

theorem tailTrace_4781107 : CollatzResearch.WordTrace tailWord_4781107 prefixEnd_4781107 2455005951575930630574595 := by
  unfold tailWord_4781107
  simp only [CollatzResearch.WordTrace]
  refine ⟨174381298289873361911997575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116254198859915574607998383 174381298289873361911997575)
  ·
    refine ⟨261571947434810042867996363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174381298289873361911997575 261571947434810042867996363)
    ·
      refine ⟨392357921152215064301994545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261571947434810042867996363 392357921152215064301994545)
      ·
        refine ⟨294268440864161298226495909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 392357921152215064301994545 294268440864161298226495909)
        ·
          refine ⟨55175332662030243417467983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 294268440864161298226495909 55175332662030243417467983)
          ·
            refine ⟨82762998993045365126201975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55175332662030243417467983 82762998993045365126201975)
            ·
              refine ⟨124144498489568047689302963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82762998993045365126201975 124144498489568047689302963)
              ·
                refine ⟨186216747734352071533954445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124144498489568047689302963 186216747734352071533954445)
                ·
                  refine ⟨69831280400382026825232917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 186216747734352071533954445 69831280400382026825232917)
                  ·
                    refine ⟨3273341268767907507432793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 69831280400382026825232917 3273341268767907507432793)
                    ·
                      refine ⟨2455005951575930630574595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3273341268767907507432793 2455005951575930630574595)
                      ·
                        rfl

theorem cell23_4781107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 6, 2].length) (baseStart_4781107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781107 prefixEnd_4781107 := by exact prefixLift 4781107
  have htrace : WordTrace (prefixWord ++ tailWord_4781107) baseStart_4781107 baseEnd_4781107 := by
    simpa [prefixWord, tailWord_4781107, baseEnd_4781107] using wordTrace_append hprefix tailTrace_4781107
  have hstable : (prefixWord ++ tailWord_4781107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781107).length < 2 ^ (prefixWord ++ tailWord_4781107).sum := by decide
  have hdescent : baseEnd_4781107 < baseStart_4781107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781120 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 6]
def baseStart_4781120 : Nat := 118140960795 + 4781120 * 2 ^ 59
def prefixEnd_4781120 : Nat := 4983230072969 + 3 ^ 40 * 4781120 * 2
def baseEnd_4781120 : Nat := 2455012626824439079712035

theorem tailTrace_4781120 : CollatzResearch.WordTrace tailWord_4781120 prefixEnd_4781120 2455012626824439079712035 := by
  unfold tailWord_4781120
  simp only [CollatzResearch.WordTrace]
  refine ⟨87190886219413132566110407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116254514959217510088147209 87190886219413132566110407)
  ·
    refine ⟨130786329329119698849165611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87190886219413132566110407 130786329329119698849165611)
    ·
      refine ⟨196179493993679548273748417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130786329329119698849165611 196179493993679548273748417)
      ·
        refine ⟨147134620495259661205311313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196179493993679548273748417 147134620495259661205311313)
        ·
          refine ⟨110350965371444745903983485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147134620495259661205311313 110350965371444745903983485)
          ·
            refine ⟨41381612014291779713993807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110350965371444745903983485 41381612014291779713993807)
            ·
              refine ⟨62072418021437669570990711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41381612014291779713993807 62072418021437669570990711)
              ·
                refine ⟨93108627032156504356486067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62072418021437669570990711 93108627032156504356486067)
                ·
                  refine ⟨139662940548234756534729101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93108627032156504356486067 139662940548234756534729101)
                  ·
                    refine ⟨52373602705588033700523413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 139662940548234756534729101 52373602705588033700523413)
                    ·
                      refine ⟨2455012626824439079712035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52373602705588033700523413 2455012626824439079712035)
                      ·
                        rfl

theorem cell23_4781120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_4781120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781120 prefixEnd_4781120 := by exact prefixLift 4781120
  have htrace : WordTrace (prefixWord ++ tailWord_4781120) baseStart_4781120 baseEnd_4781120 := by
    simpa [prefixWord, tailWord_4781120, baseEnd_4781120] using wordTrace_append hprefix tailTrace_4781120
  have hstable : (prefixWord ++ tailWord_4781120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781120).length < 2 ^ (prefixWord ++ tailWord_4781120).sum := by decide
  have hdescent : baseEnd_4781120 < baseStart_4781120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781134 : List Nat := [4, 1, 1, 1, 1, 3, 4, 1, 3, 4]
def baseStart_4781134 : Nat := 118140960795 + 4781134 * 2 ^ 59
def prefixEnd_4781134 : Nat := 4983230072969 + 3 ^ 40 * 4781134 * 2
def baseEnd_4781134 : Nat := 818339938517867341645657

theorem tailTrace_4781134 : CollatzResearch.WordTrace tailWord_4781134 prefixEnd_4781134 818339938517867341645657 := by
  unfold tailWord_4781134
  simp only [CollatzResearch.WordTrace]
  refine ⟨21797785382596943190403807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116254855373850363682153637 21797785382596943190403807)
  ·
    refine ⟨32696678073895414785605711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21797785382596943190403807 32696678073895414785605711)
    ·
      refine ⟨49045017110843122178408567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32696678073895414785605711 49045017110843122178408567)
      ·
        refine ⟨73567525666264683267612851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49045017110843122178408567 73567525666264683267612851)
        ·
          refine ⟨110351288499397024901419277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73567525666264683267612851 110351288499397024901419277)
          ·
            refine ⟨41381733187273884338032229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110351288499397024901419277 41381733187273884338032229)
            ·
              refine ⟨7759074972613853313381043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41381733187273884338032229 7759074972613853313381043)
              ·
                refine ⟨11638612458920779970071565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7759074972613853313381043 11638612458920779970071565)
                ·
                  refine ⟨4364479672095292488776837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11638612458920779970071565 4364479672095292488776837)
                  ·
                    refine ⟨818339938517867341645657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4364479672095292488776837 818339938517867341645657)
                    ·
                      rfl

theorem cell23_4781134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 3, 4].length) (baseStart_4781134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781134 prefixEnd_4781134 := by exact prefixLift 4781134
  have htrace : WordTrace (prefixWord ++ tailWord_4781134) baseStart_4781134 baseEnd_4781134 := by
    simpa [prefixWord, tailWord_4781134, baseEnd_4781134] using wordTrace_append hprefix tailTrace_4781134
  have hstable : (prefixWord ++ tailWord_4781134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781134).length < 2 ^ (prefixWord ++ tailWord_4781134).sum := by decide
  have hdescent : baseEnd_4781134 < baseStart_4781134 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781157 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 2, 5, 3]
def baseStart_4781157 : Nat := 118140960795 + 4781157 * 2 ^ 59
def prefixEnd_4781157 : Nat := 4983230072969 + 3 ^ 40 * 4781157 * 2
def baseEnd_4781157 : Nat := 2455031625608655434949365

theorem tailTrace_4781157 : CollatzResearch.WordTrace tailWord_4781157 prefixEnd_4781157 2455031625608655434949365 := by
  unfold tailWord_4781157
  simp only [CollatzResearch.WordTrace]
  refine ⟨174383121939692220451317725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116255414626461480300878483 174383121939692220451317725)
  ·
    refine ⟨65393670727384582669244147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174383121939692220451317725 65393670727384582669244147)
    ·
      refine ⟨98090506091076874003866221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65393670727384582669244147 98090506091076874003866221)
      ·
        refine ⟨36783939784153827751449833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98090506091076874003866221 36783939784153827751449833)
        ·
          refine ⟨27587954838115370813587375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36783939784153827751449833 27587954838115370813587375)
          ·
            refine ⟨41381932257173056220381063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27587954838115370813587375 41381932257173056220381063)
            ·
              refine ⟨62072898385759584330571595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41381932257173056220381063 62072898385759584330571595)
              ·
                refine ⟨93109347578639376495857393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62072898385759584330571595 93109347578639376495857393)
                ·
                  refine ⟨69832010683979532371893045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93109347578639376495857393 69832010683979532371893045)
                  ·
                    refine ⟨6546751001623081159864973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 69832010683979532371893045 6546751001623081159864973)
                    ·
                      refine ⟨2455031625608655434949365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6546751001623081159864973 2455031625608655434949365)
                      ·
                        rfl

theorem cell23_4781157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_4781157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781157 prefixEnd_4781157 := by exact prefixLift 4781157
  have htrace : WordTrace (prefixWord ++ tailWord_4781157) baseStart_4781157 baseEnd_4781157 := by
    simpa [prefixWord, tailWord_4781157, baseEnd_4781157] using wordTrace_append hprefix tailTrace_4781157
  have hstable : (prefixWord ++ tailWord_4781157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781157).length < 2 ^ (prefixWord ++ tailWord_4781157).sum := by decide
  have hdescent : baseEnd_4781157 < baseStart_4781157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781184 : List Nat := [2, 1, 1, 2, 1, 3, 3, 1, 4, 3, 2]
def baseStart_4781184 : Nat := 118140960795 + 4781184 * 2 ^ 59
def prefixEnd_4781184 : Nat := 4983230072969 + 3 ^ 40 * 4781184 * 2
def baseEnd_4781184 : Nat := 2455045489586326829311741

theorem tailTrace_4781184 : CollatzResearch.WordTrace tailWord_4781184 prefixEnd_4781184 2455045489586326829311741 := by
  unfold tailWord_4781184
  simp only [CollatzResearch.WordTrace]
  refine ⟨87192053355297202031275303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116256071140396269375033737 87192053355297202031275303)
  ·
    refine ⟨130788080032945803046912955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87192053355297202031275303 130788080032945803046912955)
    ·
      refine ⟨196182120049418704570369433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130788080032945803046912955 196182120049418704570369433)
      ·
        refine ⟨147136590037064028427777075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196182120049418704570369433 147136590037064028427777075)
        ·
          refine ⟨220704885055596042641665613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147136590037064028427777075 220704885055596042641665613)
          ·
            refine ⟨82764331895848515990624605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 220704885055596042641665613 82764331895848515990624605)
            ·
              refine ⟨31036624460943193496484227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82764331895848515990624605 31036624460943193496484227)
              ·
                refine ⟨46554936691414790244726341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31036624460943193496484227 46554936691414790244726341)
                ·
                  refine ⟨8729050629640273170886189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46554936691414790244726341 8729050629640273170886189)
                  ·
                    refine ⟨3273393986115102439082321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8729050629640273170886189 3273393986115102439082321)
                    ·
                      refine ⟨2455045489586326829311741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3273393986115102439082321 2455045489586326829311741)
                      ·
                        rfl

theorem cell23_4781184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 4, 3, 2].length) (baseStart_4781184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781184 prefixEnd_4781184 := by exact prefixLift 4781184
  have htrace : WordTrace (prefixWord ++ tailWord_4781184) baseStart_4781184 baseEnd_4781184 := by
    simpa [prefixWord, tailWord_4781184, baseEnd_4781184] using wordTrace_append hprefix tailTrace_4781184
  have hstable : (prefixWord ++ tailWord_4781184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781184).length < 2 ^ (prefixWord ++ tailWord_4781184).sum := by decide
  have hdescent : baseEnd_4781184 < baseStart_4781184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781234 : List Nat := [3, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5]
def baseStart_4781234 : Nat := 118140960795 + 4781234 * 2 ^ 59
def prefixEnd_4781234 : Nat := 4983230072969 + 3 ^ 40 * 4781234 * 2
def baseEnd_4781234 : Nat := 2455071163619051633686511

theorem tailTrace_4781234 : CollatzResearch.WordTrace tailWord_4781234 prefixEnd_4781234 2455071163619051633686511 := by
  unfold tailWord_4781234
  simp only [CollatzResearch.WordTrace]
  refine ⟨43596482590103315650467689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116257286906942175067913837 43596482590103315650467689)
  ·
    refine ⟨32697361942577486737850767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43596482590103315650467689 32697361942577486737850767)
    ·
      refine ⟨49046042913866230106776151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32697361942577486737850767 49046042913866230106776151)
      ·
        refine ⟨73569064370799345160164227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49046042913866230106776151 73569064370799345160164227)
        ·
          refine ⟨110353596556199017740246341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73569064370799345160164227 110353596556199017740246341)
          ·
            refine ⟨20691299354287315826296189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110353596556199017740246341 20691299354287315826296189)
            ·
              refine ⟨7759237257857743434861071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20691299354287315826296189 7759237257857743434861071)
              ·
                refine ⟨11638855886786615152291607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7759237257857743434861071 11638855886786615152291607)
                ·
                  refine ⟨17458283830179922728437411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11638855886786615152291607 17458283830179922728437411)
                  ·
                    refine ⟨26187425745269884092656117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17458283830179922728437411 26187425745269884092656117)
                    ·
                      refine ⟨2455071163619051633686511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26187425745269884092656117 2455071163619051633686511)
                      ·
                        rfl

theorem cell23_4781234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5].length) (baseStart_4781234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781234 prefixEnd_4781234 := by exact prefixLift 4781234
  have htrace : WordTrace (prefixWord ++ tailWord_4781234) baseStart_4781234 baseEnd_4781234 := by
    simpa [prefixWord, tailWord_4781234, baseEnd_4781234] using wordTrace_append hprefix tailTrace_4781234
  have hstable : (prefixWord ++ tailWord_4781234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781234).length < 2 ^ (prefixWord ++ tailWord_4781234).sum := by decide
  have hdescent : baseEnd_4781234 < baseStart_4781234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781241 : List Nat := [1, 2, 1, 4, 1, 4, 2, 2, 2, 4]
def baseStart_4781241 : Nat := 118140960795 + 4781241 * 2 ^ 59
def prefixEnd_4781241 : Nat := 4983230072969 + 3 ^ 40 * 4781241 * 2
def baseEnd_4781241 : Nat := 818358252661211035432993

theorem tailTrace_4781241 : CollatzResearch.WordTrace tailWord_4781241 prefixEnd_4781241 818358252661211035432993 := by
  unfold tailWord_4781241
  simp only [CollatzResearch.WordTrace]
  refine ⟨174386185671387902797375577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116257457114258601864917051 174386185671387902797375577)
  ·
    refine ⟨130789639253540927098031683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174386185671387902797375577 130789639253540927098031683)
    ·
      refine ⟨196184458880311390647047525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130789639253540927098031683 196184458880311390647047525)
      ·
        refine ⟨36784586040058385746321411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 196184458880311390647047525 36784586040058385746321411)
        ·
          refine ⟨55176879060087578619482117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36784586040058385746321411 55176879060087578619482117)
          ·
            refine ⟨10345664823766420991152897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55176879060087578619482117 10345664823766420991152897)
            ·
              refine ⟨7759248617824815743364673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10345664823766420991152897 7759248617824815743364673)
              ·
                refine ⟨5819436463368611807523505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7759248617824815743364673 5819436463368611807523505)
                ·
                  refine ⟨4364577347526458855642629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5819436463368611807523505 4364577347526458855642629)
                  ·
                    refine ⟨818358252661211035432993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4364577347526458855642629 818358252661211035432993)
                    ·
                      rfl

theorem cell23_4781241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2, 2, 4].length) (baseStart_4781241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781241 prefixEnd_4781241 := by exact prefixLift 4781241
  have htrace : WordTrace (prefixWord ++ tailWord_4781241) baseStart_4781241 baseEnd_4781241 := by
    simpa [prefixWord, tailWord_4781241, baseEnd_4781241] using wordTrace_append hprefix tailTrace_4781241
  have hstable : (prefixWord ++ tailWord_4781241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781241).length < 2 ^ (prefixWord ++ tailWord_4781241).sum := by decide
  have hdescent : baseEnd_4781241 < baseStart_4781241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781285 : List Nat := [1, 3, 1, 4, 3, 2, 2, 1, 1, 2, 3]
def baseStart_4781285 : Nat := 118140960795 + 4781285 * 2 ^ 59
def prefixEnd_4781285 : Nat := 4983230072969 + 3 ^ 40 * 4781285 * 2
def baseEnd_4781285 : Nat := 2455097351132430934148777

theorem tailTrace_4781285 : CollatzResearch.WordTrace tailWord_4781285 prefixEnd_4781285 2455097351132430934148777 := by
  unfold tailWord_4781285
  simp only [CollatzResearch.WordTrace]
  refine ⟨174387790483228498311977309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116258526988818998874651539 174387790483228498311977309)
  ·
    refine ⟨65395421431210686866991491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174387790483228498311977309 65395421431210686866991491)
    ·
      refine ⟨98093132146816030300487237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65395421431210686866991491 98093132146816030300487237)
      ·
        refine ⟨18392462277528005681341357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98093132146816030300487237 18392462277528005681341357)
        ·
          refine ⟨6897173354073002130503009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18392462277528005681341357 6897173354073002130503009)
          ·
            refine ⟨5172880015554751597877257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6897173354073002130503009 5172880015554751597877257)
            ·
              refine ⟨3879660011666063698407943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5172880015554751597877257 3879660011666063698407943)
              ·
                refine ⟨5819490017499095547611915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3879660011666063698407943 5819490017499095547611915)
                ·
                  refine ⟨8729235026248643321417873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5819490017499095547611915 8729235026248643321417873)
                  ·
                    refine ⟨6546926269686482491063405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8729235026248643321417873 6546926269686482491063405)
                    ·
                      refine ⟨2455097351132430934148777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6546926269686482491063405 2455097351132430934148777)
                      ·
                        rfl

theorem cell23_4781285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_4781285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781285 prefixEnd_4781285 := by exact prefixLift 4781285
  have htrace : WordTrace (prefixWord ++ tailWord_4781285) baseStart_4781285 baseEnd_4781285 := by
    simpa [prefixWord, tailWord_4781285, baseEnd_4781285] using wordTrace_append hprefix tailTrace_4781285
  have hstable : (prefixWord ++ tailWord_4781285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781285).length < 2 ^ (prefixWord ++ tailWord_4781285).sum := by decide
  have hdescent : baseEnd_4781285 < baseStart_4781285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781298 : List Nat := [3, 2, 1, 3, 3, 1, 1, 1, 4, 1, 3]
def baseStart_4781298 : Nat := 118140960795 + 4781298 * 2 ^ 59
def prefixEnd_4781298 : Nat := 4983230072969 + 3 ^ 40 * 4781298 * 2
def baseEnd_4781298 : Nat := 2455104026380939383286217

theorem tailTrace_4781298 : CollatzResearch.WordTrace tailWord_4781298 prefixEnd_4781298 2455104026380939383286217 := by
  unfold tailWord_4781298
  simp only [CollatzResearch.WordTrace]
  refine ⟨43597066158045350383050137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116258843088120934354800365 43597066158045350383050137)
  ·
    refine ⟨32697799618534012787287603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43597066158045350383050137 32697799618534012787287603)
    ·
      refine ⟨49046699427801019180931405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32697799618534012787287603 49046699427801019180931405)
      ·
        refine ⟨18392512285425382192849277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49046699427801019180931405 18392512285425382192849277)
        ·
          refine ⟨6897192107034518322318479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18392512285425382192849277 6897192107034518322318479)
          ·
            refine ⟨10345788160551777483477719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6897192107034518322318479 10345788160551777483477719)
            ·
              refine ⟨15518682240827666225216579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10345788160551777483477719 15518682240827666225216579)
              ·
                refine ⟨23278023361241499337824869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15518682240827666225216579 23278023361241499337824869)
                ·
                  refine ⟨4364629380232781125842163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23278023361241499337824869 4364629380232781125842163)
                  ·
                    refine ⟨6546944070349171688763245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4364629380232781125842163 6546944070349171688763245)
                    ·
                      refine ⟨2455104026380939383286217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6546944070349171688763245 2455104026380939383286217)
                      ·
                        rfl

theorem cell23_4781298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_4781298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781298 prefixEnd_4781298 := by exact prefixLift 4781298
  have htrace : WordTrace (prefixWord ++ tailWord_4781298) baseStart_4781298 baseEnd_4781298 := by
    simpa [prefixWord, tailWord_4781298, baseEnd_4781298] using wordTrace_append hprefix tailTrace_4781298
  have hstable : (prefixWord ++ tailWord_4781298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781298).length < 2 ^ (prefixWord ++ tailWord_4781298).sum := by decide
  have hdescent : baseEnd_4781298 < baseStart_4781298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781304 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 2, 8, 2]
def baseStart_4781304 : Nat := 118140960795 + 4781304 * 2 ^ 59
def prefixEnd_4781304 : Nat := 4983230072969 + 3 ^ 40 * 4781304 * 2
def baseEnd_4781304 : Nat := 2455107107264866359811189

theorem tailTrace_4781304 : CollatzResearch.WordTrace tailWord_4781304 prefixEnd_4781304 2455107107264866359811189 := by
  unfold tailWord_4781304
  simp only [CollatzResearch.WordTrace]
  refine ⟨87194241735079832278459483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116258988980106443037945977 87194241735079832278459483)
  ·
    refine ⟨130791362602619748417689225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87194241735079832278459483 130791362602619748417689225)
    ·
      refine ⟨98093521951964811313266919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130791362602619748417689225 98093521951964811313266919)
      ·
        refine ⟨147140282927947216969900379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98093521951964811313266919 147140282927947216969900379)
        ·
          refine ⟨220710424391920825454850569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147140282927947216969900379 220710424391920825454850569)
          ·
            refine ⟨165532818293940619091137927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220710424391920825454850569 165532818293940619091137927)
            ·
              refine ⟨248299227440910928636706891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165532818293940619091137927 248299227440910928636706891)
              ·
                refine ⟨372448841161366392955060337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248299227440910928636706891 372448841161366392955060337)
                ·
                  refine ⟨279336630871024794716295253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 372448841161366392955060337 279336630871024794716295253)
                  ·
                    refine ⟨3273476143019821813081585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 279336630871024794716295253 3273476143019821813081585)
                    ·
                      refine ⟨2455107107264866359811189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3273476143019821813081585 2455107107264866359811189)
                      ·
                        rfl

theorem cell23_4781304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 8, 2].length) (baseStart_4781304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781304 prefixEnd_4781304 := by exact prefixLift 4781304
  have htrace : WordTrace (prefixWord ++ tailWord_4781304) baseStart_4781304 baseEnd_4781304 := by
    simpa [prefixWord, tailWord_4781304, baseEnd_4781304] using wordTrace_append hprefix tailTrace_4781304
  have hstable : (prefixWord ++ tailWord_4781304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781304).length < 2 ^ (prefixWord ++ tailWord_4781304).sum := by decide
  have hdescent : baseEnd_4781304 < baseStart_4781304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781338 : List Nat := [3, 1, 1, 3, 3, 1, 1, 2, 4, 2, 2]
def baseStart_4781338 : Nat := 118140960795 + 4781338 * 2 ^ 59
def prefixEnd_4781338 : Nat := 4983230072969 + 3 ^ 40 * 4781338 * 2
def baseEnd_4781338 : Nat := 2455124565607119226786033

theorem tailTrace_4781338 : CollatzResearch.WordTrace tailWord_4781338 prefixEnd_4781338 2455124565607119226786033 := by
  unfold tailWord_4781338
  simp only [CollatzResearch.WordTrace]
  refine ⟨43597430888009122090914167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116259815701357658909104445 43597430888009122090914167)
  ·
    refine ⟨65396146332013683136371251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43597430888009122090914167 65396146332013683136371251)
    ·
      refine ⟨98094219498020524704556877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65396146332013683136371251 98094219498020524704556877)
      ·
        refine ⟨36785332311757696764208829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98094219498020524704556877 36785332311757696764208829)
        ·
          refine ⟨13794499616909136286578311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36785332311757696764208829 13794499616909136286578311)
          ·
            refine ⟨20691749425363704429867467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13794499616909136286578311 20691749425363704429867467)
            ·
              refine ⟨31037624138045556644801201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20691749425363704429867467 31037624138045556644801201)
              ·
                refine ⟨23278218103534167483600901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31037624138045556644801201 23278218103534167483600901)
                ·
                  refine ⟨4364665894412656403175169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23278218103534167483600901 4364665894412656403175169)
                  ·
                    refine ⟨3273499420809492302381377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4364665894412656403175169 3273499420809492302381377)
                    ·
                      refine ⟨2455124565607119226786033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3273499420809492302381377 2455124565607119226786033)
                      ·
                        rfl

theorem cell23_4781338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 4, 2, 2].length) (baseStart_4781338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781338 prefixEnd_4781338 := by exact prefixLift 4781338
  have htrace : WordTrace (prefixWord ++ tailWord_4781338) baseStart_4781338 baseEnd_4781338 := by
    simpa [prefixWord, tailWord_4781338, baseEnd_4781338] using wordTrace_append hprefix tailTrace_4781338
  have hstable : (prefixWord ++ tailWord_4781338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781338).length < 2 ^ (prefixWord ++ tailWord_4781338).sum := by decide
  have hdescent : baseEnd_4781338 < baseStart_4781338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781341 : List Nat := [1, 4, 2, 3, 1, 2, 1, 1, 2, 1, 5]
def baseStart_4781341 : Nat := 118140960795 + 4781341 * 2 ^ 59
def prefixEnd_4781341 : Nat := 4983230072969 + 3 ^ 40 * 4781341 * 2
def baseEnd_4781341 : Nat := 2455126106049082715048519

theorem tailTrace_4781341 : CollatzResearch.WordTrace tailWord_4781341 prefixEnd_4781341 2455126106049082715048519 := by
  unfold tailWord_4781341
  simp only [CollatzResearch.WordTrace]
  refine ⟨174389832971025619876015877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116259888647350413250677251 174389832971025619876015877)
  ·
    refine ⟨32698093682067303726752977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174389832971025619876015877 32698093682067303726752977)
    ·
      refine ⟨24523570261550477795064733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32698093682067303726752977 24523570261550477795064733)
      ·
        refine ⟨9196338848081429173149275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24523570261550477795064733 9196338848081429173149275)
        ·
          refine ⟨13794508272122143759723913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9196338848081429173149275 13794508272122143759723913)
          ·
            refine ⟨10345881204091607819792935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13794508272122143759723913 10345881204091607819792935)
            ·
              refine ⟨15518821806137411729689403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10345881204091607819792935 15518821806137411729689403)
              ·
                refine ⟨23278232709206117594534105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15518821806137411729689403 23278232709206117594534105)
                ·
                  refine ⟨17458674531904588195900579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23278232709206117594534105 17458674531904588195900579)
                  ·
                    refine ⟨26188011797856882293850869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17458674531904588195900579 26188011797856882293850869)
                    ·
                      refine ⟨2455126106049082715048519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26188011797856882293850869 2455126106049082715048519)
                      ·
                        rfl

theorem cell23_4781341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_4781341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781341 prefixEnd_4781341 := by exact prefixLift 4781341
  have htrace : WordTrace (prefixWord ++ tailWord_4781341) baseStart_4781341 baseEnd_4781341 := by
    simpa [prefixWord, tailWord_4781341, baseEnd_4781341] using wordTrace_append hprefix tailTrace_4781341
  have hstable : (prefixWord ++ tailWord_4781341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781341).length < 2 ^ (prefixWord ++ tailWord_4781341).sum := by decide
  have hdescent : baseEnd_4781341 < baseStart_4781341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781361 : List Nat := [1, 2, 2, 3, 3, 3, 1, 1, 7]
def baseStart_4781361 : Nat := 118140960795 + 4781361 * 2 ^ 59
def prefixEnd_4781361 : Nat := 4983230072969 + 3 ^ 40 * 4781361 * 2
def baseEnd_4781361 : Nat := 272792930629130292977603

theorem tailTrace_4781361 : CollatzResearch.WordTrace tailWord_4781361 prefixEnd_4781361 272792930629130292977603 := by
  unfold tailWord_4781361
  simp only [CollatzResearch.WordTrace]
  refine ⟨174390562430953163291743937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116260374953968775527829291 174390562430953163291743937)
  ·
    refine ⟨130792921823214872468807953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174390562430953163291743937 130792921823214872468807953)
    ·
      refine ⟨98094691367411154351605965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130792921823214872468807953 98094691367411154351605965)
      ·
        refine ⟨36785509262779182881852237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98094691367411154351605965 36785509262779182881852237)
        ·
          refine ⟨13794565973542193580694589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36785509262779182881852237 13794565973542193580694589)
          ·
            refine ⟨5172962240078322592760471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13794565973542193580694589 5172962240078322592760471)
            ·
              refine ⟨7759443360117483889140707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5172962240078322592760471 7759443360117483889140707)
              ·
                refine ⟨11639165040176225833711061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7759443360117483889140707 11639165040176225833711061)
                ·
                  refine ⟨272792930629130292977603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11639165040176225833711061 272792930629130292977603)
                  ·
                    rfl

theorem cell23_4781361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 7].length) (baseStart_4781361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781361 prefixEnd_4781361 := by exact prefixLift 4781361
  have htrace : WordTrace (prefixWord ++ tailWord_4781361) baseStart_4781361 baseEnd_4781361 := by
    simpa [prefixWord, tailWord_4781361, baseEnd_4781361] using wordTrace_append hprefix tailTrace_4781361
  have hstable : (prefixWord ++ tailWord_4781361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781361).length < 2 ^ (prefixWord ++ tailWord_4781361).sum := by decide
  have hdescent : baseEnd_4781361 < baseStart_4781361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781366 : List Nat := [5, 1, 2, 3, 2, 1, 2, 1, 2, 1, 3]
def baseStart_4781366 : Nat := 118140960795 + 4781366 * 2 ^ 59
def prefixEnd_4781366 : Nat := 4983230072969 + 3 ^ 40 * 4781366 * 2
def baseEnd_4781366 : Nat := 2455138943065445117235905

theorem tailTrace_4781366 : CollatzResearch.WordTrace tailWord_4781366 prefixEnd_4781366 2455138943065445117235905 := by
  unfold tailWord_4781366
  simp only [CollatzResearch.WordTrace]
  refine ⟨10899421549745940571604747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116260496530623366097117301 10899421549745940571604747)
  ·
    refine ⟨16349132324618910857407121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10899421549745940571604747 16349132324618910857407121)
    ·
      refine ⟨12261849243464183143055341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16349132324618910857407121 12261849243464183143055341)
      ·
        refine ⟨4598193466299068678645753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12261849243464183143055341 4598193466299068678645753)
        ·
          refine ⟨3448645099724301508984315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4598193466299068678645753 3448645099724301508984315)
          ·
            refine ⟨5172967649586452263476473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3448645099724301508984315 5172967649586452263476473)
            ·
              refine ⟨3879725737189839197607355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5172967649586452263476473 3879725737189839197607355)
              ·
                refine ⟨5819588605784758796411033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3879725737189839197607355 5819588605784758796411033)
                ·
                  refine ⟨4364691454338569097308275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5819588605784758796411033 4364691454338569097308275)
                  ·
                    refine ⟨6547037181507853645962413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4364691454338569097308275 6547037181507853645962413)
                    ·
                      refine ⟨2455138943065445117235905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6547037181507853645962413 2455138943065445117235905)
                      ·
                        rfl

theorem cell23_4781366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_4781366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781366 prefixEnd_4781366 := by exact prefixLift 4781366
  have htrace : WordTrace (prefixWord ++ tailWord_4781366) baseStart_4781366 baseEnd_4781366 := by
    simpa [prefixWord, tailWord_4781366, baseEnd_4781366] using wordTrace_append hprefix tailTrace_4781366
  have hstable : (prefixWord ++ tailWord_4781366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781366).length < 2 ^ (prefixWord ++ tailWord_4781366).sum := by decide
  have hdescent : baseEnd_4781366 < baseStart_4781366 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781372 : List Nat := [2, 2, 2, 2, 1, 5, 2, 1, 2, 2, 2]
def baseStart_4781372 : Nat := 118140960795 + 4781372 * 2 ^ 59
def prefixEnd_4781372 : Nat := 4983230072969 + 3 ^ 40 * 4781372 * 2
def baseEnd_4781372 : Nat := 2455142023949372093760877

theorem tailTrace_4781372 : CollatzResearch.WordTrace tailWord_4781372 prefixEnd_4781372 2455142023949372093760877 := by
  unfold tailWord_4781372
  simp only [CollatzResearch.WordTrace]
  refine ⟨87195481816956656085197185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116260642422608874780262913 87195481816956656085197185)
  ·
    refine ⟨65396611362717492063897889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87195481816956656085197185 65396611362717492063897889)
    ·
      refine ⟨49047458522038119047923417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65396611362717492063897889 49047458522038119047923417)
      ·
        refine ⟨36785593891528589285942563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49047458522038119047923417 36785593891528589285942563)
        ·
          refine ⟨55178390837292883928913845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36785593891528589285942563 55178390837292883928913845)
          ·
            refine ⟨5172974140996207868335673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55178390837292883928913845 5172974140996207868335673)
            ·
              refine ⟨3879730605747155901251755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5172974140996207868335673 3879730605747155901251755)
              ·
                refine ⟨5819595908620733851877633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3879730605747155901251755 5819595908620733851877633)
                ·
                  refine ⟨4364696931465550388908225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5819595908620733851877633 4364696931465550388908225)
                  ·
                    refine ⟨3273522698599162791681169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4364696931465550388908225 3273522698599162791681169)
                    ·
                      refine ⟨2455142023949372093760877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3273522698599162791681169 2455142023949372093760877)
                      ·
                        rfl

theorem cell23_4781372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 1, 2, 2, 2].length) (baseStart_4781372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781372 prefixEnd_4781372 := by exact prefixLift 4781372
  have htrace : WordTrace (prefixWord ++ tailWord_4781372) baseStart_4781372 baseEnd_4781372 := by
    simpa [prefixWord, tailWord_4781372, baseEnd_4781372] using wordTrace_append hprefix tailTrace_4781372
  have hstable : (prefixWord ++ tailWord_4781372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781372).length < 2 ^ (prefixWord ++ tailWord_4781372).sum := by decide
  have hdescent : baseEnd_4781372 < baseStart_4781372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781411 : List Nat := [1, 1, 1, 5, 2, 2, 2, 2, 2, 1, 4]
def baseStart_4781411 : Nat := 118140960795 + 4781411 * 2 ^ 59
def prefixEnd_4781411 : Nat := 4983230072969 + 3 ^ 40 * 4781411 * 2
def baseEnd_4781411 : Nat := 2455162049694897441173197

theorem tailTrace_4781411 : CollatzResearch.WordTrace tailWord_4781411 prefixEnd_4781411 2455162049694897441173197 := by
  unfold tailWord_4781411
  simp only [CollatzResearch.WordTrace]
  refine ⟨174392386080772021831064087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116261590720514681220709391 174392386080772021831064087)
  ·
    refine ⟨261588579121158032746596131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174392386080772021831064087 261588579121158032746596131)
    ·
      refine ⟨392382868681737049119894197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261588579121158032746596131 392382868681737049119894197)
      ·
        refine ⟨36785893938912848354990081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 392382868681737049119894197 36785893938912848354990081)
        ·
          refine ⟨27589420454184636266242561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36785893938912848354990081 27589420454184636266242561)
          ·
            refine ⟨20692065340638477199681921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27589420454184636266242561 20692065340638477199681921)
            ·
              refine ⟨15519049005478857899761441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20692065340638477199681921 15519049005478857899761441)
              ·
                refine ⟨11639286754109143424821081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15519049005478857899761441 11639286754109143424821081)
                ·
                  refine ⟨8729465065581857568615811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11639286754109143424821081 8729465065581857568615811)
                  ·
                    refine ⟨13094197598372786352923717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8729465065581857568615811 13094197598372786352923717)
                    ·
                      refine ⟨2455162049694897441173197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13094197598372786352923717 2455162049694897441173197)
                      ·
                        rfl

theorem cell23_4781411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_4781411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781411 prefixEnd_4781411 := by exact prefixLift 4781411
  have htrace : WordTrace (prefixWord ++ tailWord_4781411) baseStart_4781411 baseEnd_4781411 := by
    simpa [prefixWord, tailWord_4781411, baseEnd_4781411] using wordTrace_append hprefix tailTrace_4781411
  have hstable : (prefixWord ++ tailWord_4781411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781411).length < 2 ^ (prefixWord ++ tailWord_4781411).sum := by decide
  have hdescent : baseEnd_4781411 < baseStart_4781411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781448 : List Nat := [2, 1, 3, 3, 1, 2, 3, 1, 2, 2, 3]
def baseStart_4781448 : Nat := 118140960795 + 4781448 * 2 ^ 59
def prefixEnd_4781448 : Nat := 4983230072969 + 3 ^ 40 * 4781448 * 2
def baseEnd_4781448 : Nat := 2455181048479113796410527

theorem tailTrace_4781448 : CollatzResearch.WordTrace tailWord_4781448 prefixEnd_4781448 2455181048479113796410527 := by
  unfold tailWord_4781448
  simp only [CollatzResearch.WordTrace]
  refine ⟨87196867790818988575080499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116262490387758651433440665 87196867790818988575080499)
  ·
    refine ⟨130795301686228482862620749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87196867790818988575080499 130795301686228482862620749)
    ·
      refine ⟨49048238132335681073482781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130795301686228482862620749 49048238132335681073482781)
      ·
        refine ⟨18393089299625880402556043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49048238132335681073482781 18393089299625880402556043)
        ·
          refine ⟨27589633949438820603834065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18393089299625880402556043 27589633949438820603834065)
          ·
            refine ⟨20692225462079115452875549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27589633949438820603834065 20692225462079115452875549)
            ·
              refine ⟨7759584548279668294828331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20692225462079115452875549 7759584548279668294828331)
              ·
                refine ⟨11639376822419502442242497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7759584548279668294828331 11639376822419502442242497)
                ·
                  refine ⟨8729532616814626831681873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11639376822419502442242497 8729532616814626831681873)
                  ·
                    refine ⟨6547149462610970123761405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8729532616814626831681873 6547149462610970123761405)
                    ·
                      refine ⟨2455181048479113796410527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6547149462610970123761405 2455181048479113796410527)
                      ·
                        rfl

theorem cell23_4781448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_4781448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781448 prefixEnd_4781448 := by exact prefixLift 4781448
  have htrace : WordTrace (prefixWord ++ tailWord_4781448) baseStart_4781448 baseEnd_4781448 := by
    simpa [prefixWord, tailWord_4781448, baseEnd_4781448] using wordTrace_append hprefix tailTrace_4781448
  have hstable : (prefixWord ++ tailWord_4781448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781448).length < 2 ^ (prefixWord ++ tailWord_4781448).sum := by decide
  have hdescent : baseEnd_4781448 < baseStart_4781448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781468 : List Nat := [2, 2, 3, 4, 1, 1, 1, 1, 8]
def baseStart_4781468 : Nat := 118140960795 + 4781468 * 2 ^ 59
def prefixEnd_4781468 : Nat := 4983230072969 + 3 ^ 40 * 4781468 * 2
def baseEnd_4781468 : Nat := 272799035343578190906715

theorem tailTrace_4781468 : CollatzResearch.WordTrace tailWord_4781468 prefixEnd_4781468 272799035343578190906715 := by
  unfold tailWord_4781468
  simp only [CollatzResearch.WordTrace]
  refine ⟨87197232520782760282944529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116262976694377013710592705 87197232520782760282944529)
  ·
    refine ⟨65397924390587070212208397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87197232520782760282944529 65397924390587070212208397)
    ·
      refine ⟨24524221646470151329578149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65397924390587070212208397 24524221646470151329578149)
      ·
        refine ⟨4598291558713153374295903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24524221646470151329578149 4598291558713153374295903)
        ·
          refine ⟨6897437338069730061443855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4598291558713153374295903 6897437338069730061443855)
          ·
            refine ⟨10346156007104595092165783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6897437338069730061443855 10346156007104595092165783)
            ·
              refine ⟨15519234010656892638248675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10346156007104595092165783 15519234010656892638248675)
              ·
                refine ⟨23278851015985338957373013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15519234010656892638248675 23278851015985338957373013)
                ·
                  refine ⟨272799035343578190906715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23278851015985338957373013 272799035343578190906715)
                  ·
                    rfl

theorem cell23_4781468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 8].length) (baseStart_4781468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781468 prefixEnd_4781468 := by exact prefixLift 4781468
  have htrace : WordTrace (prefixWord ++ tailWord_4781468) baseStart_4781468 baseEnd_4781468 := by
    simpa [prefixWord, tailWord_4781468, baseEnd_4781468] using wordTrace_append hprefix tailTrace_4781468
  have hstable : (prefixWord ++ tailWord_4781468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781468).length < 2 ^ (prefixWord ++ tailWord_4781468).sum := by decide
  have hdescent : baseEnd_4781468 < baseStart_4781468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781485 : List Nat := [1, 5, 2, 2, 1, 2, 3, 1, 6]
def baseStart_4781485 : Nat := 118140960795 + 4781485 * 2 ^ 59
def prefixEnd_4781485 : Nat := 4983230072969 + 3 ^ 40 * 4781485 * 2
def baseEnd_4781485 : Nat := 272800005251481127960873

theorem tailTrace_4781485 : CollatzResearch.WordTrace tailWord_4781485 prefixEnd_4781485 272800005251481127960873 := by
  unfold tailWord_4781485
  simp only [CollatzResearch.WordTrace]
  refine ⟨174395085082503932469257909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116263390055002621646171939 174395085082503932469257909)
  ·
    refine ⟨16349539226484743668992929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 174395085082503932469257909 16349539226484743668992929)
    ·
      refine ⟨12262154419863557751744697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16349539226484743668992929 12262154419863557751744697)
      ·
        refine ⟨9196615814897668313808523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12262154419863557751744697 9196615814897668313808523)
        ·
          refine ⟨13794923722346502470712785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9196615814897668313808523 13794923722346502470712785)
          ·
            refine ⟨10346192791759876853034589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13794923722346502470712785 10346192791759876853034589)
            ·
              refine ⟨3879822296909953819887971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10346192791759876853034589 3879822296909953819887971)
              ·
                refine ⟨5819733445364930729831957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3879822296909953819887971 5819733445364930729831957)
                ·
                  refine ⟨272800005251481127960873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5819733445364930729831957 272800005251481127960873)
                  ·
                    rfl

theorem cell23_4781485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_4781485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781485 prefixEnd_4781485 := by exact prefixLift 4781485
  have htrace : WordTrace (prefixWord ++ tailWord_4781485) baseStart_4781485 baseEnd_4781485 := by
    simpa [prefixWord, tailWord_4781485, baseEnd_4781485] using wordTrace_append hprefix tailTrace_4781485
  have hstable : (prefixWord ++ tailWord_4781485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781485).length < 2 ^ (prefixWord ++ tailWord_4781485).sum := by decide
  have hdescent : baseEnd_4781485 < baseStart_4781485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781511 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 6, 4]
def baseStart_4781511 : Nat := 118140960795 + 4781511 * 2 ^ 59
def prefixEnd_4781511 : Nat := 4983230072969 + 3 ^ 40 * 4781511 * 2
def baseEnd_4781511 : Nat := 818404465920115683307579

theorem tailTrace_4781511 : CollatzResearch.WordTrace tailWord_4781511 prefixEnd_4781511 818404465920115683307579 := by
  unfold tailWord_4781511
  simp only [CollatzResearch.WordTrace]
  refine ⟨174396033380409738909704387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116264022253606492606469591 174396033380409738909704387)
  ·
    refine ⟨261594050070614608364556581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174396033380409738909704387 261594050070614608364556581)
    ·
      refine ⟨49048884388240239068354359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 261594050070614608364556581 49048884388240239068354359)
      ·
        refine ⟨73573326582360358602531539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49048884388240239068354359 73573326582360358602531539)
        ·
          refine ⟨110359989873540537903797309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73573326582360358602531539 110359989873540537903797309)
          ·
            refine ⟨41384996202577701713923991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110359989873540537903797309 41384996202577701713923991)
            ·
              refine ⟨62077494303866552570885987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41384996202577701713923991 62077494303866552570885987)
              ·
                refine ⟨93116241455799828856328981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62077494303866552570885987 93116241455799828856328981)
                ·
                  refine ⟨4364823818240616977640421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 93116241455799828856328981 4364823818240616977640421)
                  ·
                    refine ⟨818404465920115683307579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4364823818240616977640421 818404465920115683307579)
                    ·
                      rfl

theorem cell23_4781511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 6, 4].length) (baseStart_4781511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781511 prefixEnd_4781511 := by exact prefixLift 4781511
  have htrace : WordTrace (prefixWord ++ tailWord_4781511) baseStart_4781511 baseEnd_4781511 := by
    simpa [prefixWord, tailWord_4781511, baseEnd_4781511] using wordTrace_append hprefix tailTrace_4781511
  have hstable : (prefixWord ++ tailWord_4781511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781511).length < 2 ^ (prefixWord ++ tailWord_4781511).sum := by decide
  have hdescent : baseEnd_4781511 < baseStart_4781511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781518 : List Nat := [4, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4]
def baseStart_4781518 : Nat := 118140960795 + 4781518 * 2 ^ 59
def prefixEnd_4781518 : Nat := 4983230072969 + 3 ^ 40 * 4781518 * 2
def baseEnd_4781518 : Nat := 2455216992124928522535205

theorem tailTrace_4781518 : CollatzResearch.WordTrace tailWord_4781518 prefixEnd_4781518 2455216992124928522535205 := by
  unfold tailWord_4781518
  simp only [CollatzResearch.WordTrace]
  refine ⟨21799536086423047388151151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116264192460922919403472805 21799536086423047388151151)
  ·
    refine ⟨32699304129634571082226727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21799536086423047388151151 32699304129634571082226727)
    ·
      refine ⟨49048956194451856623340091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32699304129634571082226727 49048956194451856623340091)
      ·
        refine ⟨73573434291677784935010137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49048956194451856623340091 73573434291677784935010137)
        ·
          refine ⟨55180075718758338701257603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73573434291677784935010137 55180075718758338701257603)
          ·
            refine ⟨82770113578137508051886405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55180075718758338701257603 82770113578137508051886405)
            ·
              refine ⟨15519396295900782759728701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82770113578137508051886405 15519396295900782759728701)
              ·
                refine ⟨5819773610962793534898263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15519396295900782759728701 5819773610962793534898263)
                ·
                  refine ⟨8729660416444190302347395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5819773610962793534898263 8729660416444190302347395)
                  ·
                    refine ⟨13094490624666285453521093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8729660416444190302347395 13094490624666285453521093)
                    ·
                      refine ⟨2455216992124928522535205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13094490624666285453521093 2455216992124928522535205)
                      ·
                        rfl

theorem cell23_4781518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4].length) (baseStart_4781518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781518 prefixEnd_4781518 := by exact prefixLift 4781518
  have htrace : WordTrace (prefixWord ++ tailWord_4781518) baseStart_4781518 baseEnd_4781518 := by
    simpa [prefixWord, tailWord_4781518, baseEnd_4781518] using wordTrace_append hprefix tailTrace_4781518
  have hstable : (prefixWord ++ tailWord_4781518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781518).length < 2 ^ (prefixWord ++ tailWord_4781518).sum := by decide
  have hdescent : baseEnd_4781518 < baseStart_4781518 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781521 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 7, 2, 3]
def baseStart_4781521 : Nat := 118140960795 + 4781521 * 2 ^ 59
def prefixEnd_4781521 : Nat := 4983230072969 + 3 ^ 40 * 4781521 * 2
def baseEnd_4781521 : Nat := 2455218532566892010797691

theorem tailTrace_4781521 : CollatzResearch.WordTrace tailWord_4781521 prefixEnd_4781521 2455218532566892010797691 := by
  unfold tailWord_4781521
  simp only [CollatzResearch.WordTrace]
  refine ⟨174396398110373510617568417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116264265406915673745045611 174396398110373510617568417)
  ·
    refine ⟨130797298582780132963176313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174396398110373510617568417 130797298582780132963176313)
    ·
      refine ⟨98097973937085099722382235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130797298582780132963176313 98097973937085099722382235)
      ·
        refine ⟨147146960905627649583573353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98097973937085099722382235 147146960905627649583573353)
        ·
          refine ⟨110360220679220737187680015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147146960905627649583573353 110360220679220737187680015)
          ·
            refine ⟨165540331018831105781520023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110360220679220737187680015 165540331018831105781520023)
            ·
              refine ⟨248310496528246658672280035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165540331018831105781520023 248310496528246658672280035)
              ·
                refine ⟨372465744792369988008420053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248310496528246658672280035 372465744792369988008420053)
                ·
                  refine ⟨8729665893571171593947345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 372465744792369988008420053 8729665893571171593947345)
                  ·
                    refine ⟨6547249420178378695460509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8729665893571171593947345 6547249420178378695460509)
                    ·
                      refine ⟨2455218532566892010797691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6547249420178378695460509 2455218532566892010797691)
                      ·
                        rfl

theorem cell23_4781521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7, 2, 3].length) (baseStart_4781521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781521 prefixEnd_4781521 := by exact prefixLift 4781521
  have htrace : WordTrace (prefixWord ++ tailWord_4781521) baseStart_4781521 baseEnd_4781521 := by
    simpa [prefixWord, tailWord_4781521, baseEnd_4781521] using wordTrace_append hprefix tailTrace_4781521
  have hstable : (prefixWord ++ tailWord_4781521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781521).length < 2 ^ (prefixWord ++ tailWord_4781521).sum := by decide
  have hdescent : baseEnd_4781521 < baseStart_4781521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781541 : List Nat := [1, 3, 1, 5, 1, 1, 1, 10]
def baseStart_4781541 : Nat := 118140960795 + 4781541 * 2 ^ 59
def prefixEnd_4781541 : Nat := 4983230072969 + 3 ^ 40 * 4781541 * 2
def baseEnd_4781541 : Nat := 90934400080740071575837

theorem tailTrace_4781541 : CollatzResearch.WordTrace tailWord_4781541 prefixEnd_4781541 90934400080740071575837 := by
  unfold tailWord_4781541
  simp only [CollatzResearch.WordTrace]
  refine ⟨174397127570301054033296477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116264751713534036022197651 174397127570301054033296477)
  ·
    refine ⟨65398922838862895262486179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174397127570301054033296477 65398922838862895262486179)
    ·
      refine ⟨98098384258294342893729269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65398922838862895262486179 98098384258294342893729269)
      ·
        refine ⟨9196723524215094646287119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 98098384258294342893729269 9196723524215094646287119)
        ·
          refine ⟨13795085286322641969430679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9196723524215094646287119 13795085286322641969430679)
          ·
            refine ⟨20692627929483962954146019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13795085286322641969430679 20692627929483962954146019)
            ·
              refine ⟨31038941894225944431219029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20692627929483962954146019 31038941894225944431219029)
              ·
                refine ⟨90934400080740071575837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 31038941894225944431219029 90934400080740071575837)
                ·
                  rfl

theorem cell23_4781541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 10].length) (baseStart_4781541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781541 prefixEnd_4781541 := by exact prefixLift 4781541
  have htrace : WordTrace (prefixWord ++ tailWord_4781541) baseStart_4781541 baseEnd_4781541 := by
    simpa [prefixWord, tailWord_4781541, baseEnd_4781541] using wordTrace_append hprefix tailTrace_4781541
  have hstable : (prefixWord ++ tailWord_4781541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781541).length < 2 ^ (prefixWord ++ tailWord_4781541).sum := by decide
  have hdescent : baseEnd_4781541 < baseStart_4781541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781572 : List Nat := [2, 3, 2, 3, 3, 1, 1, 1, 1, 1, 5]
def baseStart_4781572 : Nat := 118140960795 + 4781572 * 2 ^ 59
def prefixEnd_4781572 : Nat := 4983230072969 + 3 ^ 40 * 4781572 * 2
def baseEnd_4781572 : Nat := 2455244720080271311259957

theorem tailTrace_4781572 : CollatzResearch.WordTrace tailWord_4781572 prefixEnd_4781572 2455244720080271311259957 := by
  unfold tailWord_4781572
  simp only [CollatzResearch.WordTrace]
  refine ⟨87199129116594373163837485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116265505488792497551783313 87199129116594373163837485)
  ·
    refine ⟨32699673418722889936439057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87199129116594373163837485 32699673418722889936439057)
    ·
      refine ⟨24524755064042167452329293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32699673418722889936439057 24524755064042167452329293)
      ·
        refine ⟨9196783149015812794623485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24524755064042167452329293 9196783149015812794623485)
        ·
          refine ⟨3448793680880929797983807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9196783149015812794623485 3448793680880929797983807)
          ·
            refine ⟨5173190521321394696975711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3448793680880929797983807 5173190521321394696975711)
            ·
              refine ⟨7759785781982092045463567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5173190521321394696975711 7759785781982092045463567)
              ·
                refine ⟨11639678672973138068195351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7759785781982092045463567 11639678672973138068195351)
                ·
                  refine ⟨17459518009459707102293027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11639678672973138068195351 17459518009459707102293027)
                  ·
                    refine ⟨26189277014189560653439541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17459518009459707102293027 26189277014189560653439541)
                    ·
                      refine ⟨2455244720080271311259957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26189277014189560653439541 2455244720080271311259957)
                      ·
                        rfl

theorem cell23_4781572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_4781572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781572 prefixEnd_4781572 := by exact prefixLift 4781572
  have htrace : WordTrace (prefixWord ++ tailWord_4781572) baseStart_4781572 baseEnd_4781572 := by
    simpa [prefixWord, tailWord_4781572, baseEnd_4781572] using wordTrace_append hprefix tailTrace_4781572
  have hstable : (prefixWord ++ tailWord_4781572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781572).length < 2 ^ (prefixWord ++ tailWord_4781572).sum := by decide
  have hdescent : baseEnd_4781572 < baseStart_4781572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781585 : List Nat := [1, 2, 2, 1, 1, 2, 6, 2, 2, 1, 3]
def baseStart_4781585 : Nat := 118140960795 + 4781585 * 2 ^ 59
def prefixEnd_4781585 : Nat := 4983230072969 + 3 ^ 40 * 4781585 * 2
def baseEnd_4781585 : Nat := 2455251395328779760397397

theorem tailTrace_4781585 : CollatzResearch.WordTrace tailWord_4781585 prefixEnd_4781585 2455251395328779760397397 := by
  unfold tailWord_4781585
  simp only [CollatzResearch.WordTrace]
  refine ⟨174398732382141649547898209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116265821588094433031932139 174398732382141649547898209)
  ·
    refine ⟨130799049286606237160923657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174398732382141649547898209 130799049286606237160923657)
    ·
      refine ⟨98099286964954677870692743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130799049286606237160923657 98099286964954677870692743)
      ·
        refine ⟨147148930447432016806039115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98099286964954677870692743 147148930447432016806039115)
        ·
          refine ⟨220723395671148025209058673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147148930447432016806039115 220723395671148025209058673)
          ·
            refine ⟨165542546753361018906794005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220723395671148025209058673 165542546753361018906794005)
            ·
              refine ⟨7759806879063797761255969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 165542546753361018906794005 7759806879063797761255969)
              ·
                refine ⟨5819855159297848320941977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7759806879063797761255969 5819855159297848320941977)
                ·
                  refine ⟨4364891369473386240706483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5819855159297848320941977 4364891369473386240706483)
                  ·
                    refine ⟨6547337054210079361059725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4364891369473386240706483 6547337054210079361059725)
                    ·
                      refine ⟨2455251395328779760397397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6547337054210079361059725 2455251395328779760397397)
                      ·
                        rfl

theorem cell23_4781585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2, 2, 1, 3].length) (baseStart_4781585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781585 prefixEnd_4781585 := by exact prefixLift 4781585
  have htrace : WordTrace (prefixWord ++ tailWord_4781585) baseStart_4781585 baseEnd_4781585 := by
    simpa [prefixWord, tailWord_4781585, baseEnd_4781585] using wordTrace_append hprefix tailTrace_4781585
  have hstable : (prefixWord ++ tailWord_4781585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781585).length < 2 ^ (prefixWord ++ tailWord_4781585).sum := by decide
  have hdescent : baseEnd_4781585 < baseStart_4781585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781601 : List Nat := [1, 2, 3, 2, 2, 2, 1, 1, 1, 8]
def baseStart_4781601 : Nat := 118140960795 + 4781601 * 2 ^ 59
def prefixEnd_4781601 : Nat := 4983230072969 + 3 ^ 40 * 4781601 * 2
def baseEnd_4781601 : Nat := 818419870339750565932441

theorem tailTrace_4781601 : CollatzResearch.WordTrace tailWord_4781601 prefixEnd_4781601 818419870339750565932441 := by
  unfold tailWord_4781601
  simp only [CollatzResearch.WordTrace]
  refine ⟨174399315950083684280480657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116266210633389122853653771 174399315950083684280480657)
  ·
    refine ⟨130799486962562763210360493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174399315950083684280480657 130799486962562763210360493)
    ·
      refine ⟨49049807610961036203885185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130799486962562763210360493 49049807610961036203885185)
      ·
        refine ⟨36787355708220777152913889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49049807610961036203885185 36787355708220777152913889)
        ·
          refine ⟨27590516781165582864685417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36787355708220777152913889 27590516781165582864685417)
          ·
            refine ⟨20692887585874187148514063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27590516781165582864685417 20692887585874187148514063)
            ·
              refine ⟨31039331378811280722771095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20692887585874187148514063 31039331378811280722771095)
              ·
                refine ⟨46558997068216921084156643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31039331378811280722771095 46558997068216921084156643)
                ·
                  refine ⟨69838495602325381626234965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46558997068216921084156643 69838495602325381626234965)
                  ·
                    refine ⟨818419870339750565932441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 69838495602325381626234965 818419870339750565932441)
                    ·
                      rfl

theorem cell23_4781601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_4781601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781601 prefixEnd_4781601 := by exact prefixLift 4781601
  have htrace : WordTrace (prefixWord ++ tailWord_4781601) baseStart_4781601 baseEnd_4781601 := by
    simpa [prefixWord, tailWord_4781601, baseEnd_4781601] using wordTrace_append hprefix tailTrace_4781601
  have hstable : (prefixWord ++ tailWord_4781601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781601).length < 2 ^ (prefixWord ++ tailWord_4781601).sum := by decide
  have hdescent : baseEnd_4781601 < baseStart_4781601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781625 : List Nat := [1, 2, 1, 5, 1, 2, 2, 2, 1, 4, 2]
def baseStart_4781625 : Nat := 118140960795 + 4781625 * 2 ^ 59
def prefixEnd_4781625 : Nat := 4983230072969 + 3 ^ 40 * 4781625 * 2
def baseEnd_4781625 : Nat := 2455271934554959603897213

theorem tailTrace_4781625 : CollatzResearch.WordTrace tailWord_4781625 prefixEnd_4781625 2455271934554959603897213 := by
  unfold tailWord_4781625
  simp only [CollatzResearch.WordTrace]
  refine ⟨174400191301996736379354329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116266794201331157586236219 174400191301996736379354329)
  ·
    refine ⟨130800143476497552284515747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174400191301996736379354329 130800143476497552284515747)
    ·
      refine ⟨196200215214746328426773621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130800143476497552284515747 196200215214746328426773621)
      ·
        refine ⟨18393770176382468290010027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 196200215214746328426773621 18393770176382468290010027)
        ·
          refine ⟨27590655264573702435015041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18393770176382468290010027 27590655264573702435015041)
          ·
            refine ⟨20692991448430276826261281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27590655264573702435015041 20692991448430276826261281)
            ·
              refine ⟨15519743586322707619695961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20692991448430276826261281 15519743586322707619695961)
              ·
                refine ⟨11639807689742030714771971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15519743586322707619695961 11639807689742030714771971)
                ·
                  refine ⟨17459711534613046072157957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11639807689742030714771971 17459711534613046072157957)
                  ·
                    refine ⟨3273695912739946138529617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17459711534613046072157957 3273695912739946138529617)
                    ·
                      refine ⟨2455271934554959603897213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3273695912739946138529617 2455271934554959603897213)
                      ·
                        rfl

theorem cell23_4781625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_4781625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781625 prefixEnd_4781625 := by exact prefixLift 4781625
  have htrace : WordTrace (prefixWord ++ tailWord_4781625) baseStart_4781625 baseEnd_4781625 := by
    simpa [prefixWord, tailWord_4781625, baseEnd_4781625] using wordTrace_append hprefix tailTrace_4781625
  have hstable : (prefixWord ++ tailWord_4781625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781625).length < 2 ^ (prefixWord ++ tailWord_4781625).sum := by decide
  have hdescent : baseEnd_4781625 < baseStart_4781625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781648 : List Nat := [2, 1, 1, 1, 1, 3, 3, 6, 5]
def baseStart_4781648 : Nat := 118140960795 + 4781648 * 2 ^ 59
def prefixEnd_4781648 : Nat := 4983230072969 + 3 ^ 40 * 4781648 * 2
def baseEnd_4781648 : Nat := 272809304956668112656623

theorem tailTrace_4781648 : CollatzResearch.WordTrace tailWord_4781648 prefixEnd_4781648 272809304956668112656623 := by
  unfold tailWord_4781648
  simp only [CollatzResearch.WordTrace]
  refine ⟨87200515090456705653720799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116267353453942274204961065 87200515090456705653720799)
  ·
    refine ⟨130800772635685058480581199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87200515090456705653720799 130800772635685058480581199)
    ·
      refine ⟨196201158953527587720871799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130800772635685058480581199 196201158953527587720871799)
      ·
        refine ⟨294301738430291381581307699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196201158953527587720871799 294301738430291381581307699)
        ·
          refine ⟨441452607645437072371961549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294301738430291381581307699 441452607645437072371961549)
          ·
            refine ⟨165544727867038902139485581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 441452607645437072371961549 165544727867038902139485581)
            ·
              refine ⟨62079272950139588302307093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 165544727867038902139485581 62079272950139588302307093)
              ·
                refine ⟨2909965919537793201670645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 62079272950139588302307093 2909965919537793201670645)
                ·
                  refine ⟨272809304956668112656623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2909965919537793201670645 272809304956668112656623)
                  ·
                    rfl

theorem cell23_4781648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 6, 5].length) (baseStart_4781648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781648 prefixEnd_4781648 := by exact prefixLift 4781648
  have htrace : WordTrace (prefixWord ++ tailWord_4781648) baseStart_4781648 baseEnd_4781648 := by
    simpa [prefixWord, tailWord_4781648, baseEnd_4781648] using wordTrace_append hprefix tailTrace_4781648
  have hstable : (prefixWord ++ tailWord_4781648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781648).length < 2 ^ (prefixWord ++ tailWord_4781648).sum := by decide
  have hdescent : baseEnd_4781648 < baseStart_4781648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781682 : List Nat := [3, 2, 1, 2, 3, 3, 1, 3, 5]
def baseStart_4781682 : Nat := 118140960795 + 4781682 * 2 ^ 59
def prefixEnd_4781682 : Nat := 4983230072969 + 3 ^ 40 * 4781682 * 2
def baseEnd_4781682 : Nat := 272811244772473986764939

theorem tailTrace_4781682 : CollatzResearch.WordTrace tailWord_4781682 prefixEnd_4781682 272811244772473986764939 := by
  unfold tailWord_4781682
  simp only [CollatzResearch.WordTrace]
  refine ⟨43600567565697558778544825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116268180175193490076119533 43600567565697558778544825)
  ·
    refine ⟨32700425674273169083908619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43600567565697558778544825 32700425674273169083908619)
    ·
      refine ⟨49050638511409753625862929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32700425674273169083908619 49050638511409753625862929)
      ·
        refine ⟨36787978883557315219397197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49050638511409753625862929 36787978883557315219397197)
        ·
          refine ⟨13795492081333993207273949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36787978883557315219397197 13795492081333993207273949)
          ·
            refine ⟨5173309530500247452727731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13795492081333993207273949 5173309530500247452727731)
            ·
              refine ⟨7759964295750371179091597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5173309530500247452727731 7759964295750371179091597)
              ·
                refine ⟨2909986610906389192159349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7759964295750371179091597 2909986610906389192159349)
                ·
                  refine ⟨272811244772473986764939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2909986610906389192159349 272811244772473986764939)
                  ·
                    rfl

theorem cell23_4781682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 3, 5].length) (baseStart_4781682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781682 prefixEnd_4781682 := by exact prefixLift 4781682
  have htrace : WordTrace (prefixWord ++ tailWord_4781682) baseStart_4781682 baseEnd_4781682 := by
    simpa [prefixWord, tailWord_4781682, baseEnd_4781682] using wordTrace_append hprefix tailTrace_4781682
  have hstable : (prefixWord ++ tailWord_4781682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781682).length < 2 ^ (prefixWord ++ tailWord_4781682).sum := by decide
  have hdescent : baseEnd_4781682 < baseStart_4781682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781721 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 10]
def baseStart_4781721 : Nat := 118140960795 + 4781721 * 2 ^ 59
def prefixEnd_4781721 : Nat := 4983230072969 + 3 ^ 40 * 4781721 * 2
def baseEnd_4781721 : Nat := 272813469855310136477419

theorem tailTrace_4781721 : CollatzResearch.WordTrace tailWord_4781721 prefixEnd_4781721 272813469855310136477419 := by
  unfold tailWord_4781721
  simp only [CollatzResearch.WordTrace]
  refine ⟨174403692709648944774849017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116269128473099296516566011 174403692709648944774849017)
  ·
    refine ⟨130802769532236708581136763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174403692709648944774849017 130802769532236708581136763)
    ·
      refine ⟨196204154298355062871705145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130802769532236708581136763 196204154298355062871705145)
      ·
        refine ⟨147153115723766297153778859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196204154298355062871705145 147153115723766297153778859)
        ·
          refine ⟨220729673585649445730668289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147153115723766297153778859 220729673585649445730668289)
          ·
            refine ⟨165547255189237084298001217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220729673585649445730668289 165547255189237084298001217)
            ·
              refine ⟨124160441391927813223500913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165547255189237084298001217 124160441391927813223500913)
              ·
                refine ⟨93120331043945859917625685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124160441391927813223500913 93120331043945859917625685)
                ·
                  refine ⟨272813469855310136477419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 93120331043945859917625685 272813469855310136477419)
                  ·
                    rfl

theorem cell23_4781721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 10].length) (baseStart_4781721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781721 prefixEnd_4781721 := by exact prefixLift 4781721
  have htrace : WordTrace (prefixWord ++ tailWord_4781721) baseStart_4781721 baseEnd_4781721 := by
    simpa [prefixWord, tailWord_4781721, baseEnd_4781721] using wordTrace_append hprefix tailTrace_4781721
  have hstable : (prefixWord ++ tailWord_4781721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781721).length < 2 ^ (prefixWord ++ tailWord_4781721).sum := by decide
  have hdescent : baseEnd_4781721 < baseStart_4781721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781766 : List Nat := [6, 1, 2, 1, 1, 2, 1, 1, 2, 4, 2]
def baseStart_4781766 : Nat := 118140960795 + 4781766 * 2 ^ 59
def prefixEnd_4781766 : Nat := 4983230072969 + 3 ^ 40 * 4781766 * 2
def baseEnd_4781766 : Nat := 2455344335327243552234065

theorem tailTrace_4781766 : CollatzResearch.WordTrace tailWord_4781766 prefixEnd_4781766 2455344335327243552234065 := by
  unfold tailWord_4781766
  simp only [CollatzResearch.WordTrace]
  refine ⟨5450166687327684920632411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 116270222662990611640158101 5450166687327684920632411)
  ·
    refine ⟨8175250030991527380948617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5450166687327684920632411 8175250030991527380948617)
    ·
      refine ⟨6131437523243645535711463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8175250030991527380948617 6131437523243645535711463)
      ·
        refine ⟨9197156284865468303567195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6131437523243645535711463 9197156284865468303567195)
        ·
          refine ⟨13795734427298202455350793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9197156284865468303567195 13795734427298202455350793)
          ·
            refine ⟨10346800820473651841513095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13795734427298202455350793 10346800820473651841513095)
            ·
              refine ⟨15520201230710477762269643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10346800820473651841513095 15520201230710477762269643)
              ·
                refine ⟨23280301846065716643404465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15520201230710477762269643 23280301846065716643404465)
                ·
                  refine ⟨17460226384549287482553349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23280301846065716643404465 17460226384549287482553349)
                  ·
                    refine ⟨3273792447102991402978753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17460226384549287482553349 3273792447102991402978753)
                    ·
                      refine ⟨2455344335327243552234065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3273792447102991402978753 2455344335327243552234065)
                      ·
                        rfl

theorem cell23_4781766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_4781766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781766 prefixEnd_4781766 := by exact prefixLift 4781766
  have htrace : WordTrace (prefixWord ++ tailWord_4781766) baseStart_4781766 baseEnd_4781766 := by
    simpa [prefixWord, tailWord_4781766, baseEnd_4781766] using wordTrace_append hprefix tailTrace_4781766
  have hstable : (prefixWord ++ tailWord_4781766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781766).length < 2 ^ (prefixWord ++ tailWord_4781766).sum := by decide
  have hdescent : baseEnd_4781766 < baseStart_4781766 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781768 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 5, 5]
def baseStart_4781768 : Nat := 118140960795 + 4781768 * 2 ^ 59
def prefixEnd_4781768 : Nat := 4983230072969 + 3 ^ 40 * 4781768 * 2
def baseEnd_4781768 : Nat := 818448454096184181469685

theorem tailTrace_4781768 : CollatzResearch.WordTrace tailWord_4781768 prefixEnd_4781768 818448454096184181469685 := by
  unfold tailWord_4781768
  simp only [CollatzResearch.WordTrace]
  refine ⟨87202703470239335900904979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116270271293652447867873305 87202703470239335900904979)
  ·
    refine ⟨130804055205359003851357469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87202703470239335900904979 130804055205359003851357469)
    ·
      refine ⟨49051520702009626444259051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130804055205359003851357469 49051520702009626444259051)
      ·
        refine ⟨73577281053014439666388577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49051520702009626444259051 73577281053014439666388577)
        ·
          refine ⟨55182960789760829749791433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73577281053014439666388577 55182960789760829749791433)
          ·
            refine ⟨41387220592320622312343575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55182960789760829749791433 41387220592320622312343575)
            ·
              refine ⟨62080830888480933468515363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41387220592320622312343575 62080830888480933468515363)
              ·
                refine ⟨93121246332721400202773045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62080830888480933468515363 93121246332721400202773045)
                ·
                  refine ⟨8730116843692631269009973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 93121246332721400202773045 8730116843692631269009973)
                  ·
                    refine ⟨818448454096184181469685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8730116843692631269009973 818448454096184181469685)
                    ·
                      rfl

theorem cell23_4781768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_4781768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781768 prefixEnd_4781768 := by exact prefixLift 4781768
  have htrace : WordTrace (prefixWord ++ tailWord_4781768) baseStart_4781768 baseEnd_4781768 := by
    simpa [prefixWord, tailWord_4781768, baseEnd_4781768] using wordTrace_append hprefix tailTrace_4781768
  have hstable : (prefixWord ++ tailWord_4781768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781768).length < 2 ^ (prefixWord ++ tailWord_4781768).sum := by decide
  have hdescent : baseEnd_4781768 < baseStart_4781768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781775 : List Nat := [1, 1, 2, 1, 1, 3, 1, 4, 4, 3, 2]
def baseStart_4781775 : Nat := 118140960795 + 4781775 * 2 ^ 59
def prefixEnd_4781775 : Nat := 4983230072969 + 3 ^ 40 * 4781775 * 2
def baseEnd_4781775 : Nat := 2455348956653134017021523

theorem tailTrace_4781775 : CollatzResearch.WordTrace tailWord_4781775 prefixEnd_4781775 2455348956653134017021523 := by
  unfold tailWord_4781775
  simp only [CollatzResearch.WordTrace]
  refine ⟨174405662251453311997314779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116270441500968874664876519 174405662251453311997314779)
  ·
    refine ⟨261608493377179967995972169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174405662251453311997314779 261608493377179967995972169)
    ·
      refine ⟨196206370032884975996979127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261608493377179967995972169 196206370032884975996979127)
      ·
        refine ⟨294309555049327463995468691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196206370032884975996979127 294309555049327463995468691)
        ·
          refine ⟨441464332573991195993203037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294309555049327463995468691 441464332573991195993203037)
          ·
            refine ⟨165549124715246698497451139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 441464332573991195993203037 165549124715246698497451139)
            ·
              refine ⟨248323687072870047746176709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165549124715246698497451139 248323687072870047746176709)
              ·
                refine ⟨46560691326163133952408133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 248323687072870047746176709 46560691326163133952408133)
                ·
                  refine ⟨8730129623655587616076525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46560691326163133952408133 8730129623655587616076525)
                  ·
                    refine ⟨3273798608870845356028697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8730129623655587616076525 3273798608870845356028697)
                    ·
                      refine ⟨2455348956653134017021523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3273798608870845356028697 2455348956653134017021523)
                      ·
                        rfl

theorem cell23_4781775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4, 3, 2].length) (baseStart_4781775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781775 prefixEnd_4781775 := by exact prefixLift 4781775
  have htrace : WordTrace (prefixWord ++ tailWord_4781775) baseStart_4781775 baseEnd_4781775 := by
    simpa [prefixWord, tailWord_4781775, baseEnd_4781775] using wordTrace_append hprefix tailTrace_4781775
  have hstable : (prefixWord ++ tailWord_4781775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781775).length < 2 ^ (prefixWord ++ tailWord_4781775).sum := by decide
  have hdescent : baseEnd_4781775 < baseStart_4781775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781792 : List Nat := [2, 1, 1, 3, 1, 2, 5, 1, 2, 3, 2]
def baseStart_4781792 : Nat := 118140960795 + 4781792 * 2 ^ 59
def prefixEnd_4781792 : Nat := 4983230072969 + 3 ^ 40 * 4781792 * 2
def baseEnd_4781792 : Nat := 2455357685824260450508945

theorem tailTrace_4781792 : CollatzResearch.WordTrace tailWord_4781792 prefixEnd_4781792 2455357685824260450508945 := by
  unfold tailWord_4781792
  simp only [CollatzResearch.WordTrace]
  refine ⟨87203141146195861950341815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116270854861594482600455753 87203141146195861950341815)
  ·
    refine ⟨130804711719293792925512723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87203141146195861950341815 130804711719293792925512723)
    ·
      refine ⟨196207067578940689388269085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130804711719293792925512723 196207067578940689388269085)
      ·
        refine ⟨73577650342102758520600907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196207067578940689388269085 73577650342102758520600907)
        ·
          refine ⟨110366475513154137780901361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73577650342102758520600907 110366475513154137780901361)
          ·
            refine ⟨82774856634865603335676021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110366475513154137780901361 82774856634865603335676021)
            ·
              refine ⟨7760142809518650312719627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82774856634865603335676021 7760142809518650312719627)
              ·
                refine ⟨11640214214277975469079441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7760142809518650312719627 11640214214277975469079441)
                ·
                  refine ⟨8730160660708481601809581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11640214214277975469079441 8730160660708481601809581)
                  ·
                    refine ⟨3273810247765680600678593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8730160660708481601809581 3273810247765680600678593)
                    ·
                      refine ⟨2455357685824260450508945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3273810247765680600678593 2455357685824260450508945)
                      ·
                        rfl

theorem cell23_4781792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 2, 3, 2].length) (baseStart_4781792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781792 prefixEnd_4781792 := by exact prefixLift 4781792
  have htrace : WordTrace (prefixWord ++ tailWord_4781792) baseStart_4781792 baseEnd_4781792 := by
    simpa [prefixWord, tailWord_4781792, baseEnd_4781792] using wordTrace_append hprefix tailTrace_4781792
  have hstable : (prefixWord ++ tailWord_4781792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781792).length < 2 ^ (prefixWord ++ tailWord_4781792).sum := by decide
  have hdescent : baseEnd_4781792 < baseStart_4781792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781802 : List Nat := [3, 1, 3, 1, 1, 1, 6, 1, 1, 5]
def baseStart_4781802 : Nat := 118140960795 + 4781802 * 2 ^ 59
def prefixEnd_4781802 : Nat := 4983230072969 + 3 ^ 40 * 4781802 * 2
def baseEnd_4781802 : Nat := 818454273543601803794633

theorem tailTrace_4781802 : CollatzResearch.WordTrace tailWord_4781802 prefixEnd_4781802 818454273543601803794633 := by
  unfold tailWord_4781802
  simp only [CollatzResearch.WordTrace]
  refine ⟨43601661755588873902136915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116271098014903663739031773 43601661755588873902136915)
  ·
    refine ⟨65402492633383310853205373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43601661755588873902136915 65402492633383310853205373)
    ·
      refine ⟨24525934737518741569952015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65402492633383310853205373 24525934737518741569952015)
      ·
        refine ⟨36788902106278112354928023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24525934737518741569952015 36788902106278112354928023)
        ·
          refine ⟨55183353159417168532392035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36788902106278112354928023 55183353159417168532392035)
          ·
            refine ⟨82775029739125752798588053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55183353159417168532392035 82775029739125752798588053)
            ·
              refine ⟨3880079519021519662433815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 82775029739125752798588053 3880079519021519662433815)
              ·
                refine ⟨5820119278532279493650723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3880079519021519662433815 5820119278532279493650723)
                ·
                  refine ⟨8730178917798419240476085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5820119278532279493650723 8730178917798419240476085)
                  ·
                    refine ⟨818454273543601803794633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8730178917798419240476085 818454273543601803794633)
                    ·
                      rfl

theorem cell23_4781802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_4781802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781802 prefixEnd_4781802 := by exact prefixLift 4781802
  have htrace : WordTrace (prefixWord ++ tailWord_4781802) baseStart_4781802 baseEnd_4781802 := by
    simpa [prefixWord, tailWord_4781802, baseEnd_4781802] using wordTrace_append hprefix tailTrace_4781802
  have hstable : (prefixWord ++ tailWord_4781802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781802).length < 2 ^ (prefixWord ++ tailWord_4781802).sum := by decide
  have hdescent : baseEnd_4781802 < baseStart_4781802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781818 : List Nat := [3, 1, 1, 1, 1, 3, 1, 4, 1, 1, 6]
def baseStart_4781818 : Nat := 118140960795 + 4781818 * 2 ^ 59
def prefixEnd_4781818 : Nat := 4983230072969 + 3 ^ 40 * 4781818 * 2
def baseEnd_4781818 : Nat := 2455371036321277348783825

theorem tailTrace_4781818 : CollatzResearch.WordTrace tailWord_4781818 prefixEnd_4781818 2455371036321277348783825 := by
  unfold tailWord_4781818
  simp only [CollatzResearch.WordTrace]
  refine ⟨43601807647574382585282527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116271487060198353560753405 43601807647574382585282527)
  ·
    refine ⟨65402711471361573877923791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43601807647574382585282527 65402711471361573877923791)
    ·
      refine ⟨98104067207042360816885687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65402711471361573877923791 98104067207042360816885687)
      ·
        refine ⟨147156100810563541225328531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98104067207042360816885687 147156100810563541225328531)
        ·
          refine ⟨220734151215845311837992797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147156100810563541225328531 220734151215845311837992797)
          ·
            refine ⟨82775306705941991939247299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 220734151215845311837992797 82775306705941991939247299)
            ·
              refine ⟨124162960058912987908870949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82775306705941991939247299 124162960058912987908870949)
              ·
                refine ⟨23280555011046185232913303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 124162960058912987908870949 23280555011046185232913303)
                ·
                  refine ⟨34920832516569277849369955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23280555011046185232913303 34920832516569277849369955)
                  ·
                    refine ⟨52381248774853916774054933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34920832516569277849369955 52381248774853916774054933)
                    ·
                      refine ⟨2455371036321277348783825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52381248774853916774054933 2455371036321277348783825)
                      ·
                        rfl

theorem cell23_4781818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 1, 1, 6].length) (baseStart_4781818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781818 prefixEnd_4781818 := by exact prefixLift 4781818
  have htrace : WordTrace (prefixWord ++ tailWord_4781818) baseStart_4781818 baseEnd_4781818 := by
    simpa [prefixWord, tailWord_4781818, baseEnd_4781818] using wordTrace_append hprefix tailTrace_4781818
  have hstable : (prefixWord ++ tailWord_4781818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781818).length < 2 ^ (prefixWord ++ tailWord_4781818).sum := by decide
  have hdescent : baseEnd_4781818 < baseStart_4781818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781825 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 5, 2, 3]
def baseStart_4781825 : Nat := 118140960795 + 4781825 * 2 ^ 59
def prefixEnd_4781825 : Nat := 4983230072969 + 3 ^ 40 * 4781825 * 2
def baseEnd_4781825 : Nat := 2455374630685858821396293

theorem tailTrace_4781825 : CollatzResearch.WordTrace tailWord_4781825 prefixEnd_4781825 2455374630685858821396293 := by
  unfold tailWord_4781825
  simp only [CollatzResearch.WordTrace]
  refine ⟨174407485901272170536634929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116271657267514780357756619 174407485901272170536634929)
  ·
    refine ⟨130805614425954127902476197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174407485901272170536634929 130805614425954127902476197)
    ·
      refine ⟨24526052704866398981714287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130805614425954127902476197 24526052704866398981714287)
      ·
        refine ⟨36789079057299598472571431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24526052704866398981714287 36789079057299598472571431)
        ·
          refine ⟨55183618585949397708857147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36789079057299598472571431 55183618585949397708857147)
          ·
            refine ⟨82775427878924096563285721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55183618585949397708857147 82775427878924096563285721)
            ·
              refine ⟨62081570909193072422464291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82775427878924096563285721 62081570909193072422464291)
              ·
                refine ⟨93122356363789608633696437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62081570909193072422464291 93122356363789608633696437)
                ·
                  refine ⟨8730220909105275809409041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 93122356363789608633696437 8730220909105275809409041)
                  ·
                    refine ⟨6547665681828956857056781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8730220909105275809409041 6547665681828956857056781)
                    ·
                      refine ⟨2455374630685858821396293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6547665681828956857056781 2455374630685858821396293)
                      ·
                        rfl

theorem cell23_4781825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_4781825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781825 prefixEnd_4781825 := by exact prefixLift 4781825
  have htrace : WordTrace (prefixWord ++ tailWord_4781825) baseStart_4781825 baseEnd_4781825 := by
    simpa [prefixWord, tailWord_4781825, baseEnd_4781825] using wordTrace_append hprefix tailTrace_4781825
  have hstable : (prefixWord ++ tailWord_4781825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781825).length < 2 ^ (prefixWord ++ tailWord_4781825).sum := by decide
  have hdescent : baseEnd_4781825 < baseStart_4781825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781835 : List Nat := [1, 1, 1, 1, 5, 1, 5, 1, 1, 2, 4]
def baseStart_4781835 : Nat := 118140960795 + 4781835 * 2 ^ 59
def prefixEnd_4781835 : Nat := 4983230072969 + 3 ^ 40 * 4781835 * 2
def baseEnd_4781835 : Nat := 2455379765492403782271247

theorem tailTrace_4781835 : CollatzResearch.WordTrace tailWord_4781835 prefixEnd_4781835 2455379765492403782271247 := by
  unfold tailWord_4781835
  simp only [CollatzResearch.WordTrace]
  refine ⟨174407850631235942244498959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116271900420823961496332639 174407850631235942244498959)
  ·
    refine ⟨261611775946853913366748439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174407850631235942244498959 261611775946853913366748439)
    ·
      refine ⟨392417663920280870050122659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261611775946853913366748439 392417663920280870050122659)
      ·
        refine ⟨588626495880421305075183989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 392417663920280870050122659 588626495880421305075183989)
        ·
          refine ⟨55183733988789497350798499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 588626495880421305075183989 55183733988789497350798499)
          ·
            refine ⟨82775600983184246026197749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55183733988789497350798499 82775600983184246026197749)
            ·
              refine ⟨7760212592173523064956039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82775600983184246026197749 7760212592173523064956039)
              ·
                refine ⟨11640318888260284597434059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7760212592173523064956039 11640318888260284597434059)
                ·
                  refine ⟨17460478332390426896151089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11640318888260284597434059 17460478332390426896151089)
                  ·
                    refine ⟨13095358749292820172113317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17460478332390426896151089 13095358749292820172113317)
                    ·
                      refine ⟨2455379765492403782271247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13095358749292820172113317 2455379765492403782271247)
                      ·
                        rfl

theorem cell23_4781835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 2, 4].length) (baseStart_4781835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781835 prefixEnd_4781835 := by exact prefixLift 4781835
  have htrace : WordTrace (prefixWord ++ tailWord_4781835) baseStart_4781835 baseEnd_4781835 := by
    simpa [prefixWord, tailWord_4781835, baseEnd_4781835] using wordTrace_append hprefix tailTrace_4781835
  have hstable : (prefixWord ++ tailWord_4781835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781835).length < 2 ^ (prefixWord ++ tailWord_4781835).sum := by decide
  have hdescent : baseEnd_4781835 < baseStart_4781835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781845 : List Nat := [1, 3, 2, 1, 2, 3, 4, 7]
def baseStart_4781845 : Nat := 118140960795 + 4781845 * 2 ^ 59
def prefixEnd_4781845 : Nat := 4983230072969 + 3 ^ 40 * 4781845 * 2
def baseEnd_4781845 : Nat := 90940181492553657153563

theorem tailTrace_4781845 : CollatzResearch.WordTrace tailWord_4781845 prefixEnd_4781845 90940181492553657153563 := by
  unfold tailWord_4781845
  simp only [CollatzResearch.WordTrace]
  refine ⟨174408215361199713952362989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116272143574133142634908659 174408215361199713952362989)
  ·
    refine ⟨65403080760449892732136121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174408215361199713952362989 65403080760449892732136121)
    ·
      refine ⟨49052310570337419549102091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65403080760449892732136121 49052310570337419549102091)
      ·
        refine ⟨73578465855506129323653137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49052310570337419549102091 73578465855506129323653137)
        ·
          refine ⟨55183849391629596992739853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73578465855506129323653137 55183849391629596992739853)
          ·
            refine ⟨20693943521861098872277445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55183849391629596992739853 20693943521861098872277445)
            ·
              refine ⟨3880114410348956038552021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20693943521861098872277445 3880114410348956038552021)
              ·
                refine ⟨90940181492553657153563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3880114410348956038552021 90940181492553657153563)
                ·
                  rfl

theorem cell23_4781845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 7].length) (baseStart_4781845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781845 prefixEnd_4781845 := by exact prefixLift 4781845
  have htrace : WordTrace (prefixWord ++ tailWord_4781845) baseStart_4781845 baseEnd_4781845 := by
    simpa [prefixWord, tailWord_4781845, baseEnd_4781845] using wordTrace_append hprefix tailTrace_4781845
  have hstable : (prefixWord ++ tailWord_4781845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781845).length < 2 ^ (prefixWord ++ tailWord_4781845).sum := by decide
  have hdescent : baseEnd_4781845 < baseStart_4781845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781855 : List Nat := [1, 1, 2, 4, 2, 1, 2, 1, 3, 3, 3]
def baseStart_4781855 : Nat := 118140960795 + 4781855 * 2 ^ 59
def prefixEnd_4781855 : Nat := 4983230072969 + 3 ^ 40 * 4781855 * 2
def baseEnd_4781855 : Nat := 2455390035105493704021155

theorem tailTrace_4781855 : CollatzResearch.WordTrace tailWord_4781855 prefixEnd_4781855 2455390035105493704021155 := by
  unfold tailWord_4781855
  simp only [CollatzResearch.WordTrace]
  refine ⟨174408580091163485660227019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116272386727442323773484679 174408580091163485660227019)
  ·
    refine ⟨261612870136745228490340529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174408580091163485660227019 261612870136745228490340529)
    ·
      refine ⟨196209652602558921367755397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261612870136745228490340529 196209652602558921367755397)
      ·
        refine ⟨36789309862979797756454137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 196209652602558921367755397 36789309862979797756454137)
        ·
          refine ⟨27591982397234848317340603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36789309862979797756454137 27591982397234848317340603)
          ·
            refine ⟨41387973595852272476010905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27591982397234848317340603 41387973595852272476010905)
            ·
              refine ⟨31040980196889204357008179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41387973595852272476010905 31040980196889204357008179)
              ·
                refine ⟨46561470295333806535512269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31040980196889204357008179 46561470295333806535512269)
                ·
                  refine ⟨17460551360750177450817101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46561470295333806535512269 17460551360750177450817101)
                  ·
                    refine ⟨6547706760281316544056413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17460551360750177450817101 6547706760281316544056413)
                    ·
                      refine ⟨2455390035105493704021155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6547706760281316544056413 2455390035105493704021155)
                      ·
                        rfl

theorem cell23_4781855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_4781855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781855 prefixEnd_4781855 := by exact prefixLift 4781855
  have htrace : WordTrace (prefixWord ++ tailWord_4781855) baseStart_4781855 baseEnd_4781855 := by
    simpa [prefixWord, tailWord_4781855, baseEnd_4781855] using wordTrace_append hprefix tailTrace_4781855
  have hstable : (prefixWord ++ tailWord_4781855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781855).length < 2 ^ (prefixWord ++ tailWord_4781855).sum := by decide
  have hdescent : baseEnd_4781855 < baseStart_4781855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781873 : List Nat := [1, 2, 2, 3, 2, 3, 3, 2, 1, 2, 2]
def baseStart_4781873 : Nat := 118140960795 + 4781873 * 2 ^ 59
def prefixEnd_4781873 : Nat := 4983230072969 + 3 ^ 40 * 4781873 * 2
def baseEnd_4781873 : Nat := 2455399277757274633596073

theorem tailTrace_4781873 : CollatzResearch.WordTrace tailWord_4781873 prefixEnd_4781873 2455399277757274633596073 := by
  unfold tailWord_4781873
  simp only [CollatzResearch.WordTrace]
  refine ⟨174409236605098274734382273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116272824403398849822921515 174409236605098274734382273)
  ·
    refine ⟨130806927453823706050786705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174409236605098274734382273 130806927453823706050786705)
    ·
      refine ⟨98105195590367779538090029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130806927453823706050786705 98105195590367779538090029)
      ·
        refine ⟨36789448346387917326783761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98105195590367779538090029 36789448346387917326783761)
        ·
          refine ⟨27592086259790937995087821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36789448346387917326783761 27592086259790937995087821)
          ·
            refine ⟨10347032347421601748157933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27592086259790937995087821 10347032347421601748157933)
            ·
              refine ⟨3880137130283100655559225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10347032347421601748157933 3880137130283100655559225)
              ·
                refine ⟨2910102847712325491669419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3880137130283100655559225 2910102847712325491669419)
                ·
                  refine ⟨4365154271568488237504129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2910102847712325491669419 4365154271568488237504129)
                  ·
                    refine ⟨3273865703676366178128097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4365154271568488237504129 3273865703676366178128097)
                    ·
                      refine ⟨2455399277757274633596073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3273865703676366178128097 2455399277757274633596073)
                      ·
                        rfl

theorem cell23_4781873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 2, 1, 2, 2].length) (baseStart_4781873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781873 prefixEnd_4781873 := by exact prefixLift 4781873
  have htrace : WordTrace (prefixWord ++ tailWord_4781873) baseStart_4781873 baseEnd_4781873 := by
    simpa [prefixWord, tailWord_4781873, baseEnd_4781873] using wordTrace_append hprefix tailTrace_4781873
  have hstable : (prefixWord ++ tailWord_4781873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781873).length < 2 ^ (prefixWord ++ tailWord_4781873).sum := by decide
  have hdescent : baseEnd_4781873 < baseStart_4781873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4781925 : List Nat := [1, 3, 1, 3, 1, 1, 1, 4, 2, 2, 4]
def baseStart_4781925 : Nat := 118140960795 + 4781925 * 2 ^ 59
def prefixEnd_4781925 : Nat := 4983230072969 + 3 ^ 40 * 4781925 * 2
def baseEnd_4781925 : Nat := 2455425978751308430145833

theorem tailTrace_4781925 : CollatzResearch.WordTrace tailWord_4781925 prefixEnd_4781925 2455425978751308430145833 := by
  unfold tailWord_4781925
  simp only [CollatzResearch.WordTrace]
  refine ⟨174411133200909887615275229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116274088800606591743516819 174411133200909887615275229)
  ·
    refine ⟨65404174950341207855728211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174411133200909887615275229 65404174950341207855728211)
    ·
      refine ⟨98106262425511811783592317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65404174950341207855728211 98106262425511811783592317)
      ·
        refine ⟨36789848409566929418847119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98106262425511811783592317 36789848409566929418847119)
        ·
          refine ⟨55184772614350394128270679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36789848409566929418847119 55184772614350394128270679)
          ·
            refine ⟨82777158921525591192406019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55184772614350394128270679 82777158921525591192406019)
            ·
              refine ⟨124165738382288386788609029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82777158921525591192406019 124165738382288386788609029)
              ·
                refine ⟨23281075946679072522864193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 124165738382288386788609029 23281075946679072522864193)
                ·
                  refine ⟨17460806960009304392148145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23281075946679072522864193 17460806960009304392148145)
                  ·
                    refine ⟨13095605220006978294111109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17460806960009304392148145 13095605220006978294111109)
                    ·
                      refine ⟨2455425978751308430145833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13095605220006978294111109 2455425978751308430145833)
                      ·
                        rfl

theorem cell23_4781925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_4781925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4781925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4781925 prefixEnd_4781925 := by exact prefixLift 4781925
  have htrace : WordTrace (prefixWord ++ tailWord_4781925) baseStart_4781925 baseEnd_4781925 := by
    simpa [prefixWord, tailWord_4781925, baseEnd_4781925] using wordTrace_append hprefix tailTrace_4781925
  have hstable : (prefixWord ++ tailWord_4781925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4781925).length < 2 ^ (prefixWord ++ tailWord_4781925).sum := by decide
  have hdescent : baseEnd_4781925 < baseStart_4781925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4781925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4782015 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 2, 4, 4]
def baseStart_4782015 : Nat := 118140960795 + 4782015 * 2 ^ 59
def prefixEnd_4782015 : Nat := 4983230072969 + 3 ^ 40 * 4782015 * 2
def baseEnd_4782015 : Nat := 2455472192010213078020419

theorem tailTrace_4782015 : CollatzResearch.WordTrace tailWord_4782015 prefixEnd_4782015 2455472192010213078020419 := by
  unfold tailWord_4782015
  simp only [CollatzResearch.WordTrace]
  refine ⟨174414415770583832986051499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116276277180389221990700999 174414415770583832986051499)
  ·
    refine ⟨261621623655875749479077249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174414415770583832986051499 261621623655875749479077249)
    ·
      refine ⟨196216217741906812109307937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261621623655875749479077249 196216217741906812109307937)
      ·
        refine ⟨147162163306430109081980953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196216217741906812109307937 147162163306430109081980953)
        ·
          refine ⟨110371622479822581811485715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147162163306430109081980953 110371622479822581811485715)
          ·
            refine ⟨165557433719733872717228573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110371622479822581811485715 165557433719733872717228573)
            ·
              refine ⟨62084037644900202268960715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 165557433719733872717228573 62084037644900202268960715)
              ·
                refine ⟨93126056467350303403441073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62084037644900202268960715 93126056467350303403441073)
                ·
                  refine ⟨69844542350512727552580805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93126056467350303403441073 69844542350512727552580805)
                  ·
                    refine ⟨13095851690721136416108901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 69844542350512727552580805 13095851690721136416108901)
                    ·
                      refine ⟨2455472192010213078020419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13095851690721136416108901 2455472192010213078020419)
                      ·
                        rfl

theorem cell23_4782015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4, 4].length) (baseStart_4782015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4782015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4782015 prefixEnd_4782015 := by exact prefixLift 4782015
  have htrace : WordTrace (prefixWord ++ tailWord_4782015) baseStart_4782015 baseEnd_4782015 := by
    simpa [prefixWord, tailWord_4782015, baseEnd_4782015] using wordTrace_append hprefix tailTrace_4782015
  have hstable : (prefixWord ++ tailWord_4782015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4782015).length < 2 ^ (prefixWord ++ tailWord_4782015).sum := by decide
  have hdescent : baseEnd_4782015 < baseStart_4782015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4782015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4782109 : List Nat := [1, 4, 2, 2, 2, 1, 1, 2, 3, 1, 4]
def baseStart_4782109 : Nat := 118140960795 + 4782109 * 2 ^ 59
def prefixEnd_4782109 : Nat := 4983230072969 + 3 ^ 40 * 4782109 * 2
def baseEnd_4782109 : Nat := 2455520459191735710244987

theorem tailTrace_4782109 : CollatzResearch.WordTrace tailWord_4782109 prefixEnd_4782109 2455520459191735710244987 := by
  unfold tailWord_4782109
  simp only [CollatzResearch.WordTrace]
  refine ⟨174417844232243287039973381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116278562821495524693315587 174417844232243287039973381)
  ·
    refine ⟨32703345793545616319995009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174417844232243287039973381 32703345793545616319995009)
    ·
      refine ⟨24527509345159212239996257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32703345793545616319995009 24527509345159212239996257)
      ·
        refine ⟨18395632008869409179997193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24527509345159212239996257 18395632008869409179997193)
        ·
          refine ⟨13796724006652056884997895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18395632008869409179997193 13796724006652056884997895)
          ·
            refine ⟨20695086009978085327496843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13796724006652056884997895 20695086009978085327496843)
            ·
              refine ⟨31042629014967127991245265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20695086009978085327496843 31042629014967127991245265)
              ·
                refine ⟨23281971761225345993433949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31042629014967127991245265 23281971761225345993433949)
                ·
                  refine ⟨8730739410459504747537731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23281971761225345993433949 8730739410459504747537731)
                  ·
                    refine ⟨13096109115689257121306597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8730739410459504747537731 13096109115689257121306597)
                    ·
                      refine ⟨2455520459191735710244987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13096109115689257121306597 2455520459191735710244987)
                      ·
                        rfl

theorem cell23_4782109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_4782109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4782109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4782109 prefixEnd_4782109 := by exact prefixLift 4782109
  have htrace : WordTrace (prefixWord ++ tailWord_4782109) baseStart_4782109 baseEnd_4782109 := by
    simpa [prefixWord, tailWord_4782109, baseEnd_4782109] using wordTrace_append hprefix tailTrace_4782109
  have hstable : (prefixWord ++ tailWord_4782109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4782109).length < 2 ^ (prefixWord ++ tailWord_4782109).sum := by decide
  have hdescent : baseEnd_4782109 < baseStart_4782109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4782109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4782129 : List Nat := [1, 2, 2, 3, 1, 3, 2, 1, 3, 2, 3]
def baseStart_4782129 : Nat := 118140960795 + 4782129 * 2 ^ 59
def prefixEnd_4782129 : Nat := 4983230072969 + 3 ^ 40 * 4782129 * 2
def baseEnd_4782129 : Nat := 2455530728804825631994895

theorem tailTrace_4782129 : CollatzResearch.WordTrace tailWord_4782129 prefixEnd_4782129 2455530728804825631994895 := by
  unfold tailWord_4782129
  simp only [CollatzResearch.WordTrace]
  refine ⟨174418573692170830455701441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116279049128113886970467627 174418573692170830455701441)
  ·
    refine ⟨130813930269128122841776081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174418573692170830455701441 130813930269128122841776081)
    ·
      refine ⟨98110447701846092131332061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130813930269128122841776081 98110447701846092131332061)
      ·
        refine ⟨36791417888192284549249523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98110447701846092131332061 36791417888192284549249523)
        ·
          refine ⟨55187126832288426823874285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36791417888192284549249523 55187126832288426823874285)
          ·
            refine ⟨20695172562108160058952857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55187126832288426823874285 20695172562108160058952857)
            ·
              refine ⟨15521379421581120044214643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20695172562108160058952857 15521379421581120044214643)
              ·
                refine ⟨23282069132371680066321965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15521379421581120044214643 23282069132371680066321965)
                ·
                  refine ⟨8730775924639380024870737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23282069132371680066321965 8730775924639380024870737)
                  ·
                    refine ⟨6548081943479535018653053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8730775924639380024870737 6548081943479535018653053)
                    ·
                      refine ⟨2455530728804825631994895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6548081943479535018653053 2455530728804825631994895)
                      ·
                        rfl

theorem cell23_4782129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_4782129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4782129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4782129 prefixEnd_4782129 := by exact prefixLift 4782129
  have htrace : WordTrace (prefixWord ++ tailWord_4782129) baseStart_4782129 baseEnd_4782129 := by
    simpa [prefixWord, tailWord_4782129, baseEnd_4782129] using wordTrace_append hprefix tailTrace_4782129
  have hstable : (prefixWord ++ tailWord_4782129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4782129).length < 2 ^ (prefixWord ++ tailWord_4782129).sum := by decide
  have hdescent : baseEnd_4782129 < baseStart_4782129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4782129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4782143 : List Nat := [1, 1, 2, 2, 3, 1, 3, 5, 1, 2, 2]
def baseStart_4782143 : Nat := 118140960795 + 4782143 * 2 ^ 59
def prefixEnd_4782143 : Nat := 4983230072969 + 3 ^ 40 * 4782143 * 2
def baseEnd_4782143 : Nat := 2455537917533988577219831

theorem tailTrace_4782143 : CollatzResearch.WordTrace tailWord_4782143 prefixEnd_4782143 2455537917533988577219831 := by
  unfold tailWord_4782143
  simp only [CollatzResearch.WordTrace]
  refine ⟨174419084314120110846711083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116279389542746740564474055 174419084314120110846711083)
  ·
    refine ⟨261628626471180166270066625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174419084314120110846711083 261628626471180166270066625)
    ·
      refine ⟨196221469853385124702549969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261628626471180166270066625 196221469853385124702549969)
      ·
        refine ⟨147166102390038843526912477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196221469853385124702549969 147166102390038843526912477)
        ·
          refine ⟨55187288396264566322592179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147166102390038843526912477 55187288396264566322592179)
          ·
            refine ⟨82780932594396849483888269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55187288396264566322592179 82780932594396849483888269)
            ·
              refine ⟨31042849722898818556458101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82780932594396849483888269 31042849722898818556458101)
              ·
                refine ⟨2910267161521764239667947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31042849722898818556458101 2910267161521764239667947)
                ·
                  refine ⟨4365400742282646359501921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2910267161521764239667947 4365400742282646359501921)
                  ·
                    refine ⟨3274050556711984769626441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4365400742282646359501921 3274050556711984769626441)
                    ·
                      refine ⟨2455537917533988577219831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3274050556711984769626441 2455537917533988577219831)
                      ·
                        rfl

theorem cell23_4782143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 5, 1, 2, 2].length) (baseStart_4782143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4782143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4782143 prefixEnd_4782143 := by exact prefixLift 4782143
  have htrace : WordTrace (prefixWord ++ tailWord_4782143) baseStart_4782143 baseEnd_4782143 := by
    simpa [prefixWord, tailWord_4782143, baseEnd_4782143] using wordTrace_append hprefix tailTrace_4782143
  have hstable : (prefixWord ++ tailWord_4782143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4782143).length < 2 ^ (prefixWord ++ tailWord_4782143).sum := by decide
  have hdescent : baseEnd_4782143 < baseStart_4782143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4782143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4782159 : List Nat := [1, 1, 2, 1, 1, 2, 2, 5, 4, 1, 3]
def baseStart_4782159 : Nat := 118140960795 + 4782159 * 2 ^ 59
def prefixEnd_4782159 : Nat := 4983230072969 + 3 ^ 40 * 4782159 * 2
def baseEnd_4782159 : Nat := 2455546133224460514619757

theorem tailTrace_4782159 : CollatzResearch.WordTrace tailWord_4782159 prefixEnd_4782159 2455546133224460514619757 := by
  unfold tailWord_4782159
  simp only [CollatzResearch.WordTrace]
  refine ⟨174419667882062145579293531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116279778588041430386195687 174419667882062145579293531)
  ·
    refine ⟨261629501823093218368940297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174419667882062145579293531 261629501823093218368940297)
    ·
      refine ⟨196222126367319913776705223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261629501823093218368940297 196222126367319913776705223)
      ·
        refine ⟨294333189550979870665057835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196222126367319913776705223 294333189550979870665057835)
        ·
          refine ⟨441499784326469805997586753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294333189550979870665057835 441499784326469805997586753)
          ·
            refine ⟨331124838244852354498190065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 441499784326469805997586753 331124838244852354498190065)
            ·
              refine ⟨248343628683639265873642549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 331124838244852354498190065 248343628683639265873642549)
              ·
                refine ⟨23282215189091181175653989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 248343628683639265873642549 23282215189091181175653989)
                ·
                  refine ⟨4365415347954596470435123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23282215189091181175653989 4365415347954596470435123)
                  ·
                    refine ⟨6548123021931894705652685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4365415347954596470435123 6548123021931894705652685)
                    ·
                      refine ⟨2455546133224460514619757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6548123021931894705652685 2455546133224460514619757)
                      ·
                        rfl

theorem cell23_4782159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 4, 1, 3].length) (baseStart_4782159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4782159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4782159 prefixEnd_4782159 := by exact prefixLift 4782159
  have htrace : WordTrace (prefixWord ++ tailWord_4782159) baseStart_4782159 baseEnd_4782159 := by
    simpa [prefixWord, tailWord_4782159, baseEnd_4782159] using wordTrace_append hprefix tailTrace_4782159
  have hstable : (prefixWord ++ tailWord_4782159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4782159).length < 2 ^ (prefixWord ++ tailWord_4782159).sum := by decide
  have hdescent : baseEnd_4782159 < baseStart_4782159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4782159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4782173 : List Nat := [1, 4, 4, 1, 1, 3, 1, 1, 1, 2, 4]
def baseStart_4782173 : Nat := 118140960795 + 4782173 * 2 ^ 59
def prefixEnd_4782173 : Nat := 4983230072969 + 3 ^ 40 * 4782173 * 2
def baseEnd_4782173 : Nat := 2455553321953623459844693

theorem tailTrace_4782173 : CollatzResearch.WordTrace tailWord_4782173 prefixEnd_4782173 2455553321953623459844693 := by
  unfold tailWord_4782173
  simp only [CollatzResearch.WordTrace]
  refine ⟨174420178504011425970303173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116280119002674283980202115 174420178504011425970303173)
  ·
    refine ⟨32703783469502142369431845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174420178504011425970303173 32703783469502142369431845)
    ·
      refine ⟨6131959400531651694268471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32703783469502142369431845 6131959400531651694268471)
      ·
        refine ⟨9197939100797477541402707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6131959400531651694268471 9197939100797477541402707)
        ·
          refine ⟨13796908651196216312104061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9197939100797477541402707 13796908651196216312104061)
          ·
            refine ⟨5173840744198581117039023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13796908651196216312104061 5173840744198581117039023)
            ·
              refine ⟨7760761116297871675558535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5173840744198581117039023 7760761116297871675558535)
              ·
                refine ⟨11641141674446807513337803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7760761116297871675558535 11641141674446807513337803)
                ·
                  refine ⟨17461712511670211270006705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11641141674446807513337803 17461712511670211270006705)
                  ·
                    refine ⟨13096284383752658452505029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17461712511670211270006705 13096284383752658452505029)
                    ·
                      refine ⟨2455553321953623459844693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13096284383752658452505029 2455553321953623459844693)
                      ·
                        rfl

theorem cell23_4782173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_4782173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4782173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4782173 prefixEnd_4782173 := by exact prefixLift 4782173
  have htrace : WordTrace (prefixWord ++ tailWord_4782173) baseStart_4782173 baseEnd_4782173 := by
    simpa [prefixWord, tailWord_4782173, baseEnd_4782173] using wordTrace_append hprefix tailTrace_4782173
  have hstable : (prefixWord ++ tailWord_4782173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4782173).length < 2 ^ (prefixWord ++ tailWord_4782173).sum := by decide
  have hdescent : baseEnd_4782173 < baseStart_4782173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4782173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4782176 : List Nat := [2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 3]
def baseStart_4782176 : Nat := 118140960795 + 4782176 * 2 ^ 59
def prefixEnd_4782176 : Nat := 4983230072969 + 3 ^ 40 * 4782176 * 2
def baseEnd_4782176 : Nat := 2455554862395586948107179

theorem tailTrace_4782176 : CollatzResearch.WordTrace tailWord_4782176 prefixEnd_4782176 2455554862395586948107179 := by
  unfold tailWord_4782176
  simp only [CollatzResearch.WordTrace]
  refine ⟨87210143961500278741331191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116280191948667038321774921 87210143961500278741331191)
  ·
    refine ⟨130815215942250418111996787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87210143961500278741331191 130815215942250418111996787)
    ·
      refine ⟨196222823913375627167995181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130815215942250418111996787 196222823913375627167995181)
      ·
        refine ⟨73583558967515860187998193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196222823913375627167995181 73583558967515860187998193)
        ·
          refine ⟨55187669225636895140998645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73583558967515860187998193 55187669225636895140998645)
          ·
            refine ⟨5173843989903458919468623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55187669225636895140998645 5173843989903458919468623)
            ·
              refine ⟨7760765984855188379202935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5173843989903458919468623 7760765984855188379202935)
              ·
                refine ⟨11641148977282782568804403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7760765984855188379202935 11641148977282782568804403)
                ·
                  refine ⟨17461723465924173853206605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11641148977282782568804403 17461723465924173853206605)
                  ·
                    refine ⟨6548146299721565194952477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17461723465924173853206605 6548146299721565194952477)
                    ·
                      refine ⟨2455554862395586948107179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6548146299721565194952477 2455554862395586948107179)
                      ·
                        rfl

theorem cell23_4782176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 3].length) (baseStart_4782176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4782176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4782176 prefixEnd_4782176 := by exact prefixLift 4782176
  have htrace : WordTrace (prefixWord ++ tailWord_4782176) baseStart_4782176 baseEnd_4782176 := by
    simpa [prefixWord, tailWord_4782176, baseEnd_4782176] using wordTrace_append hprefix tailTrace_4782176
  have hstable : (prefixWord ++ tailWord_4782176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4782176).length < 2 ^ (prefixWord ++ tailWord_4782176).sum := by decide
  have hdescent : baseEnd_4782176 < baseStart_4782176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4782176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4782250 : List Nat := [3, 1, 5, 1, 2, 1, 1, 2, 1, 4, 2]
def baseStart_4782250 : Nat := 118140960795 + 4782250 * 2 ^ 59
def prefixEnd_4782250 : Nat := 4983230072969 + 3 ^ 40 * 4782250 * 2
def baseEnd_4782250 : Nat := 2455592859964019658581839

theorem tailTrace_4782250 : CollatzResearch.WordTrace tailWord_4782250 prefixEnd_4782250 2455592859964019658581839 := by
  unfold tailWord_4782250
  simp only [CollatzResearch.WordTrace]
  refine ⟨43605746731183117030214051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116281991283154978747237469 43605746731183117030214051)
  ·
    refine ⟨65408620096774675545321077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43605746731183117030214051 65408620096774675545321077)
    ·
      refine ⟨6132058134072625832373851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65408620096774675545321077 6132058134072625832373851)
      ·
        refine ⟨9198087201108938748560777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6132058134072625832373851 9198087201108938748560777)
        ·
          refine ⟨6898565400831704061420583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9198087201108938748560777 6898565400831704061420583)
          ·
            refine ⟨10347848101247556092130875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6898565400831704061420583 10347848101247556092130875)
            ·
              refine ⟨15521772151871334138196313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10347848101247556092130875 15521772151871334138196313)
              ·
                refine ⟨11641329113903500603647235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15521772151871334138196313 11641329113903500603647235)
                ·
                  refine ⟨17461993670855250905470853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11641329113903500603647235 17461993670855250905470853)
                  ·
                    refine ⟨3274123813285359544775785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17461993670855250905470853 3274123813285359544775785)
                    ·
                      refine ⟨2455592859964019658581839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3274123813285359544775785 2455592859964019658581839)
                      ·
                        rfl

theorem cell23_4782250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_4782250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4782250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4782250 prefixEnd_4782250 := by exact prefixLift 4782250
  have htrace : WordTrace (prefixWord ++ tailWord_4782250) baseStart_4782250 baseEnd_4782250 := by
    simpa [prefixWord, tailWord_4782250, baseEnd_4782250] using wordTrace_append hprefix tailTrace_4782250
  have hstable : (prefixWord ++ tailWord_4782250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4782250).length < 2 ^ (prefixWord ++ tailWord_4782250).sum := by decide
  have hdescent : baseEnd_4782250 < baseStart_4782250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4782250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4782252 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 5, 7]
def baseStart_4782252 : Nat := 118140960795 + 4782252 * 2 ^ 59
def prefixEnd_4782252 : Nat := 4983230072969 + 3 ^ 40 * 4782252 * 2
def baseEnd_4782252 : Nat := 818531295641776216918943

theorem tailTrace_4782252 : CollatzResearch.WordTrace tailWord_4782252 prefixEnd_4782252 818531295641776216918943 := by
  unfold tailWord_4782252
  simp only [CollatzResearch.WordTrace]
  refine ⟨87211529935362611231214505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116282039913816814974952673 87211529935362611231214505)
  ·
    refine ⟨65408647451521958423410879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87211529935362611231214505 65408647451521958423410879)
    ·
      refine ⟨98112971177282937635116319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65408647451521958423410879 98112971177282937635116319)
      ·
        refine ⟨147169456765924406452674479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98112971177282937635116319 147169456765924406452674479)
        ·
          refine ⟨220754185148886609679011719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147169456765924406452674479 220754185148886609679011719)
          ·
            refine ⟨331131277723329914518517579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220754185148886609679011719 331131277723329914518517579)
            ·
              refine ⟨496696916584994871777776369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 331131277723329914518517579 496696916584994871777776369)
              ·
                refine ⟨372522687438746153833332277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 496696916584994871777776369 372522687438746153833332277)
                ·
                  refine ⟨34924001947382451921874901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 372522687438746153833332277 34924001947382451921874901)
                  ·
                    refine ⟨818531295641776216918943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34924001947382451921874901 818531295641776216918943)
                    ·
                      rfl

theorem cell23_4782252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 7].length) (baseStart_4782252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4782252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4782252 prefixEnd_4782252 := by exact prefixLift 4782252
  have htrace : WordTrace (prefixWord ++ tailWord_4782252) baseStart_4782252 baseEnd_4782252 := by
    simpa [prefixWord, tailWord_4782252, baseEnd_4782252] using wordTrace_append hprefix tailTrace_4782252
  have hstable : (prefixWord ++ tailWord_4782252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4782252).length < 2 ^ (prefixWord ++ tailWord_4782252).sum := by decide
  have hdescent : baseEnd_4782252 < baseStart_4782252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4782252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4782254 : List Nat := [4, 1, 4, 2, 1, 1, 3, 1, 1, 3, 2]
def baseStart_4782254 : Nat := 118140960795 + 4782254 * 2 ^ 59
def prefixEnd_4782254 : Nat := 4983230072969 + 3 ^ 40 * 4782254 * 2
def baseEnd_4782254 : Nat := 2455594913886637642931821

theorem tailTrace_4782254 : CollatzResearch.WordTrace tailWord_4782254 prefixEnd_4782254 2455594913886637642931821 := by
  unfold tailWord_4782254
  simp only [CollatzResearch.WordTrace]
  refine ⟨21802891602089747100500227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116282088544478651202667877 21802891602089747100500227)
  ·
    refine ⟨32704337403134620650750341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21802891602089747100500227 32704337403134620650750341)
    ·
      refine ⟨6132063263087741372015689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32704337403134620650750341 6132063263087741372015689)
      ·
        refine ⟨4599047447315806029011767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6132063263087741372015689 4599047447315806029011767)
        ·
          refine ⟨6898571170973709043517651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4599047447315806029011767 6898571170973709043517651)
          ·
            refine ⟨10347856756460563565276477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6898571170973709043517651 10347856756460563565276477)
            ·
              refine ⟨3880446283672711336978679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10347856756460563565276477 3880446283672711336978679)
              ·
                refine ⟨5820669425509067005468019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3880446283672711336978679 5820669425509067005468019)
                ·
                  refine ⟨8731004138263600508202029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5820669425509067005468019 8731004138263600508202029)
                  ·
                    refine ⟨3274126551848850190575761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8731004138263600508202029 3274126551848850190575761)
                    ·
                      refine ⟨2455594913886637642931821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3274126551848850190575761 2455594913886637642931821)
                      ·
                        rfl

theorem cell23_4782254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_4782254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4782254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4782254 prefixEnd_4782254 := by exact prefixLift 4782254
  have htrace : WordTrace (prefixWord ++ tailWord_4782254) baseStart_4782254 baseEnd_4782254 := by
    simpa [prefixWord, tailWord_4782254, baseEnd_4782254] using wordTrace_append hprefix tailTrace_4782254
  have hstable : (prefixWord ++ tailWord_4782254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4782254).length < 2 ^ (prefixWord ++ tailWord_4782254).sum := by decide
  have hdescent : baseEnd_4782254 < baseStart_4782254 := by decide
  rcases family_descends (prefixWord ++ tailWord_4782254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4782289 : List Nat := [1, 2, 2, 1, 2, 2, 2, 2, 4, 1, 4]
def baseStart_4782289 : Nat := 118140960795 + 4782289 * 2 ^ 59
def prefixEnd_4782289 : Nat := 4983230072969 + 3 ^ 40 * 4782289 * 2
def baseEnd_4782289 : Nat := 2455612885709545005994159

theorem tailTrace_4782289 : CollatzResearch.WordTrace tailWord_4782289 prefixEnd_4782289 2455612885709545005994159 := by
  unfold tailWord_4782289
  simp only [CollatzResearch.WordTrace]
  refine ⟨174424409371591177781525921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116282939581060785187683947 174424409371591177781525921)
  ·
    refine ⟨130818307028693383336144441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174424409371591177781525921 130818307028693383336144441)
    ·
      refine ⟨98113730271520037502108331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130818307028693383336144441 98113730271520037502108331)
      ·
        refine ⟨147170595407280056253162497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98113730271520037502108331 147170595407280056253162497)
        ·
          refine ⟨110377946555460042189871873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147170595407280056253162497 110377946555460042189871873)
          ·
            refine ⟨82783459916595031642403905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110377946555460042189871873 82783459916595031642403905)
            ·
              refine ⟨62087594937446273731802929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82783459916595031642403905 62087594937446273731802929)
              ·
                refine ⟨46565696203084705298852197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62087594937446273731802929 46565696203084705298852197)
                ·
                  refine ⟨8731068038078382243534787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46565696203084705298852197 8731068038078382243534787)
                  ·
                    refine ⟨13096602057117573365302181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8731068038078382243534787 13096602057117573365302181)
                    ·
                      refine ⟨2455612885709545005994159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13096602057117573365302181 2455612885709545005994159)
                      ·
                        rfl

theorem cell23_4782289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4, 1, 4].length) (baseStart_4782289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4782289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4782289 prefixEnd_4782289 := by exact prefixLift 4782289
  have htrace : WordTrace (prefixWord ++ tailWord_4782289) baseStart_4782289 baseEnd_4782289 := by
    simpa [prefixWord, tailWord_4782289, baseEnd_4782289] using wordTrace_append hprefix tailTrace_4782289
  have hstable : (prefixWord ++ tailWord_4782289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4782289).length < 2 ^ (prefixWord ++ tailWord_4782289).sum := by decide
  have hdescent : baseEnd_4782289 < baseStart_4782289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4782289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4782299 : List Nat := [1, 1, 1, 1, 1, 1, 1, 7, 5, 4]
def baseStart_4782299 : Nat := 118140960795 + 4782299 * 2 ^ 59
def prefixEnd_4782299 : Nat := 4983230072969 + 3 ^ 40 * 4782299 * 2
def baseEnd_4782299 : Nat := 818539340172029988956371

theorem tailTrace_4782299 : CollatzResearch.WordTrace tailWord_4782299 prefixEnd_4782299 818539340172029988956371 := by
  unfold tailWord_4782299
  simp only [CollatzResearch.WordTrace]
  refine ⟨174424774101554949489389951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116283182734369966326259967 174424774101554949489389951)
  ·
    refine ⟨261637161152332424234084927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174424774101554949489389951 261637161152332424234084927)
    ·
      refine ⟨392455741728498636351127391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261637161152332424234084927 392455741728498636351127391)
      ·
        refine ⟨588683612592747954526691087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 392455741728498636351127391 588683612592747954526691087)
        ·
          refine ⟨883025418889121931790036631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 588683612592747954526691087 883025418889121931790036631)
          ·
            refine ⟨1324538128333682897685054947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 883025418889121931790036631 1324538128333682897685054947)
            ·
              refine ⟨1986807192500524346527582421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1324538128333682897685054947 1986807192500524346527582421)
              ·
                refine ⟨46565793574231039371740213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1986807192500524346527582421 46565793574231039371740213)
                ·
                  refine ⟨4365543147584159941100645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46565793574231039371740213 4365543147584159941100645)
                  ·
                    refine ⟨818539340172029988956371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4365543147584159941100645 818539340172029988956371)
                    ·
                      rfl

theorem cell23_4782299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 5, 4].length) (baseStart_4782299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4782299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4782299 prefixEnd_4782299 := by exact prefixLift 4782299
  have htrace : WordTrace (prefixWord ++ tailWord_4782299) baseStart_4782299 baseEnd_4782299 := by
    simpa [prefixWord, tailWord_4782299, baseEnd_4782299] using wordTrace_append hprefix tailTrace_4782299
  have hstable : (prefixWord ++ tailWord_4782299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4782299).length < 2 ^ (prefixWord ++ tailWord_4782299).sum := by decide
  have hdescent : baseEnd_4782299 < baseStart_4782299 := by decide
  rcases family_descends (prefixWord ++ tailWord_4782299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4782319 : List Nat := [1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 6]
def baseStart_4782319 : Nat := 118140960795 + 4782319 * 2 ^ 59
def prefixEnd_4782319 : Nat := 4983230072969 + 3 ^ 40 * 4782319 * 2
def baseEnd_4782319 : Nat := 2455628290129179888619021

theorem tailTrace_4782319 : CollatzResearch.WordTrace tailWord_4782319 prefixEnd_4782319 2455628290129179888619021 := by
  unfold tailWord_4782319
  simp only [CollatzResearch.WordTrace]
  refine ⟨174425503561482492905118011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116283669040988328603412007 174425503561482492905118011)
  ·
    refine ⟨261638255342223739357677017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174425503561482492905118011 261638255342223739357677017)
    ·
      refine ⟨196228691506667804518257763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261638255342223739357677017 196228691506667804518257763)
      ·
        refine ⟨294343037260001706777386645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196228691506667804518257763 294343037260001706777386645)
        ·
          refine ⟨13797329871562580005189999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 294343037260001706777386645 13797329871562580005189999)
          ·
            refine ⟨20695994807343870007784999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13797329871562580005189999 20695994807343870007784999)
            ·
              refine ⟨31043992211015805011677499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20695994807343870007784999 31043992211015805011677499)
              ·
                refine ⟨46565988316523707517516249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31043992211015805011677499 46565988316523707517516249)
                ·
                  refine ⟨34924491237392780638137187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46565988316523707517516249 34924491237392780638137187)
                  ·
                    refine ⟨52386736856089170957205781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34924491237392780638137187 52386736856089170957205781)
                    ·
                      refine ⟨2455628290129179888619021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52386736856089170957205781 2455628290129179888619021)
                      ·
                        rfl

theorem cell23_4782319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 6].length) (baseStart_4782319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4782319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4782319 prefixEnd_4782319 := by exact prefixLift 4782319
  have htrace : WordTrace (prefixWord ++ tailWord_4782319) baseStart_4782319 baseEnd_4782319 := by
    simpa [prefixWord, tailWord_4782319, baseEnd_4782319] using wordTrace_append hprefix tailTrace_4782319
  have hstable : (prefixWord ++ tailWord_4782319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4782319).length < 2 ^ (prefixWord ++ tailWord_4782319).sum := by decide
  have hdescent : baseEnd_4782319 < baseStart_4782319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4782319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4782329 : List Nat := [1, 2, 1, 3, 1, 1, 2, 6, 6]
def baseStart_4782329 : Nat := 118140960795 + 4782329 * 2 ^ 59
def prefixEnd_4782329 : Nat := 4983230072969 + 3 ^ 40 * 4782329 * 2
def baseEnd_4782329 : Nat := 272848158326191649943775

theorem tailTrace_4782329 : CollatzResearch.WordTrace tailWord_4782329 prefixEnd_4782329 272848158326191649943775 := by
  unfold tailWord_4782329
  simp only [CollatzResearch.WordTrace]
  refine ⟨174425868291446264612982041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116283912194297509741988027 174425868291446264612982041)
  ·
    refine ⟨130819401218584698459736531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174425868291446264612982041 130819401218584698459736531)
    ·
      refine ⟨196229101827877047689604797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130819401218584698459736531 196229101827877047689604797)
      ·
        refine ⟨73585913185453892883601799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196229101827877047689604797 73585913185453892883601799)
        ·
          refine ⟨110378869778180839325402699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73585913185453892883601799 110378869778180839325402699)
          ·
            refine ⟨165568304667271258988104049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110378869778180839325402699 165568304667271258988104049)
            ·
              refine ⟨124176228500453444241078037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165568304667271258988104049 124176228500453444241078037)
              ·
                refine ⟨5820760710958755198800533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 124176228500453444241078037 5820760710958755198800533)
                ·
                  refine ⟨272848158326191649943775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5820760710958755198800533 272848158326191649943775)
                  ·
                    rfl

theorem cell23_4782329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6, 6].length) (baseStart_4782329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4782329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4782329 prefixEnd_4782329 := by exact prefixLift 4782329
  have htrace : WordTrace (prefixWord ++ tailWord_4782329) baseStart_4782329 baseEnd_4782329 := by
    simpa [prefixWord, tailWord_4782329, baseEnd_4782329] using wordTrace_append hprefix tailTrace_4782329
  have hstable : (prefixWord ++ tailWord_4782329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4782329).length < 2 ^ (prefixWord ++ tailWord_4782329).sum := by decide
  have hdescent : baseEnd_4782329 < baseStart_4782329 := by decide
  rcases family_descends (prefixWord ++ tailWord_4782329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4782396 : List Nat := [2, 2, 2, 2, 1, 2, 2, 2, 3, 1, 4]
def baseStart_4782396 : Nat := 118140960795 + 4782396 * 2 ^ 59
def prefixEnd_4782396 : Nat := 4983230072969 + 3 ^ 40 * 4782396 * 2
def baseEnd_4782396 : Nat := 2455667828139576087356167

theorem tailTrace_4782396 : CollatzResearch.WordTrace tailWord_4782396 prefixEnd_4782396 2455667828139576087356167 := by
  unfold tailWord_4782396
  simp only [CollatzResearch.WordTrace]
  refine ⟨87214155991101767527835521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116285541321469023370447361 87214155991101767527835521)
  ·
    refine ⟨65410616993326325645876641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87214155991101767527835521 65410616993326325645876641)
    ·
      refine ⟨49057962744994744234407481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65410616993326325645876641 49057962744994744234407481)
      ·
        refine ⟨36793472058746058175805611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49057962744994744234407481 36793472058746058175805611)
        ·
          refine ⟨55190208088119087263708417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36793472058746058175805611 55190208088119087263708417)
          ·
            refine ⟨41392656066089315447781313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55190208088119087263708417 41392656066089315447781313)
            ·
              refine ⟨31044492049566986585835985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41392656066089315447781313 31044492049566986585835985)
              ·
                refine ⟨23283369037175239939376989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31044492049566986585835985 23283369037175239939376989)
                ·
                  refine ⟨8731263388940714977266371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23283369037175239939376989 8731263388940714977266371)
                  ·
                    refine ⟨13096895083411072465899557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8731263388940714977266371 13096895083411072465899557)
                    ·
                      refine ⟨2455667828139576087356167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13096895083411072465899557 2455667828139576087356167)
                      ·
                        rfl

theorem cell23_4782396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_4782396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4782396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4782396 prefixEnd_4782396 := by exact prefixLift 4782396
  have htrace : WordTrace (prefixWord ++ tailWord_4782396) baseStart_4782396 baseEnd_4782396 := by
    simpa [prefixWord, tailWord_4782396, baseEnd_4782396] using wordTrace_append hprefix tailTrace_4782396
  have hstable : (prefixWord ++ tailWord_4782396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4782396).length < 2 ^ (prefixWord ++ tailWord_4782396).sum := by decide
  have hdescent : baseEnd_4782396 < baseStart_4782396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4782396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4782440 : List Nat := [2, 1, 4, 2, 2, 2, 2, 2, 2, 4]
def baseStart_4782440 : Nat := 118140960795 + 4782440 * 2 ^ 59
def prefixEnd_4782440 : Nat := 4983230072969 + 3 ^ 40 * 4782440 * 2
def baseEnd_4782440 : Nat := 818563473762791305068655

theorem tailTrace_4782440 : CollatzResearch.WordTrace tailWord_4782440 prefixEnd_4782440 818563473762791305068655 := by
  unfold tailWord_4782440
  simp only [CollatzResearch.WordTrace]
  refine ⟨87214958397022065285136387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116286611196029420380181849 87214958397022065285136387)
  ·
    refine ⟨130822437595533097927704581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87214958397022065285136387 130822437595533097927704581)
    ·
      refine ⟨24529207049162455861444609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130822437595533097927704581 24529207049162455861444609)
      ·
        refine ⟨18396905286871841896083457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24529207049162455861444609 18396905286871841896083457)
        ·
          refine ⟨13797678965153881422062593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18396905286871841896083457 13797678965153881422062593)
          ·
            refine ⟨10348259223865411066546945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13797678965153881422062593 10348259223865411066546945)
            ·
              refine ⟨7761194417899058299910209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10348259223865411066546945 7761194417899058299910209)
              ·
                refine ⟨5820895813424293724932657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7761194417899058299910209 5820895813424293724932657)
                ·
                  refine ⟨4365671860068220293699493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5820895813424293724932657 4365671860068220293699493)
                  ·
                    refine ⟨818563473762791305068655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4365671860068220293699493 818563473762791305068655)
                    ·
                      rfl

theorem cell23_4782440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_4782440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4782440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4782440 prefixEnd_4782440 := by exact prefixLift 4782440
  have htrace : WordTrace (prefixWord ++ tailWord_4782440) baseStart_4782440 baseEnd_4782440 := by
    simpa [prefixWord, tailWord_4782440, baseEnd_4782440] using wordTrace_append hprefix tailTrace_4782440
  have hstable : (prefixWord ++ tailWord_4782440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4782440).length < 2 ^ (prefixWord ++ tailWord_4782440).sum := by decide
  have hdescent : baseEnd_4782440 < baseStart_4782440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4782440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4782453 : List Nat := [1, 3, 4, 1, 2, 3, 1, 8]
def baseStart_4782453 : Nat := 118140960795 + 4782453 * 2 ^ 59
def prefixEnd_4782453 : Nat := 4983230072969 + 3 ^ 40 * 4782453 * 2
def baseEnd_4782453 : Nat := 90951744316180828309015

theorem tailTrace_4782453 : CollatzResearch.WordTrace tailWord_4782453 prefixEnd_4782453 90951744316180828309015 := by
  unfold tailWord_4782453
  simp only [CollatzResearch.WordTrace]
  refine ⟨174430390942997033790496013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116286927295331355860330675 174430390942997033790496013)
  ·
    refine ⟨65411396603623887671436005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174430390942997033790496013 65411396603623887671436005)
    ·
      refine ⟨12264636863179478938394251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65411396603623887671436005 12264636863179478938394251)
      ·
        refine ⟨18396955294769218407591377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12264636863179478938394251 18396955294769218407591377)
        ·
          refine ⟨13797716471076913805693533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18396955294769218407591377 13797716471076913805693533)
          ·
            refine ⟨5174143676653842677135075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13797716471076913805693533 5174143676653842677135075)
            ·
              refine ⟨7761215514980764015702613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5174143676653842677135075 7761215514980764015702613)
              ·
                refine ⟨90951744316180828309015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7761215514980764015702613 90951744316180828309015)
                ·
                  rfl

theorem cell23_4782453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 8].length) (baseStart_4782453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4782453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4782453 prefixEnd_4782453 := by exact prefixLift 4782453
  have htrace : WordTrace (prefixWord ++ tailWord_4782453) baseStart_4782453 baseEnd_4782453 := by
    simpa [prefixWord, tailWord_4782453, baseEnd_4782453] using wordTrace_append hprefix tailTrace_4782453
  have hstable : (prefixWord ++ tailWord_4782453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4782453).length < 2 ^ (prefixWord ++ tailWord_4782453).sum := by decide
  have hdescent : baseEnd_4782453 < baseStart_4782453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4782453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4782484 : List Nat := [2, 4, 2, 1, 3, 2, 2, 1, 1, 2, 3]
def baseStart_4782484 : Nat := 118140960795 + 4782484 * 2 ^ 59
def prefixEnd_4782484 : Nat := 4983230072969 + 3 ^ 40 * 4782484 * 2
def baseEnd_4782484 : Nat := 2455713014437171743055763

theorem tailTrace_4782484 : CollatzResearch.WordTrace tailWord_4782484 prefixEnd_4782484 2455713014437171743055763 := by
  unfold tailWord_4782484
  simp only [CollatzResearch.WordTrace]
  refine ⟨87215760802942363042437253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116287681070589817389916337 87215760802942363042437253)
  ·
    refine ⟨16352955150551693070456985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87215760802942363042437253 16352955150551693070456985)
    ·
      refine ⟨12264716362913769802842739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16352955150551693070456985 12264716362913769802842739)
      ·
        refine ⟨18397074544370654704264109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12264716362913769802842739 18397074544370654704264109)
        ·
          refine ⟨6898902954138995514099041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18397074544370654704264109 6898902954138995514099041)
          ·
            refine ⟨5174177215604246635574281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6898902954138995514099041 5174177215604246635574281)
            ·
              refine ⟨3880632911703184976680711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5174177215604246635574281 3880632911703184976680711)
              ·
                refine ⟨5820949367554777465021067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3880632911703184976680711 5820949367554777465021067)
                ·
                  refine ⟨8731424051332166197531601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5820949367554777465021067 8731424051332166197531601)
                  ·
                    refine ⟨6548568038499124648148701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8731424051332166197531601 6548568038499124648148701)
                    ·
                      refine ⟨2455713014437171743055763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6548568038499124648148701 2455713014437171743055763)
                      ·
                        rfl

theorem cell23_4782484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_4782484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4782484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4782484 prefixEnd_4782484 := by exact prefixLift 4782484
  have htrace : WordTrace (prefixWord ++ tailWord_4782484) baseStart_4782484 baseEnd_4782484 := by
    simpa [prefixWord, tailWord_4782484, baseEnd_4782484] using wordTrace_append hprefix tailTrace_4782484
  have hstable : (prefixWord ++ tailWord_4782484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4782484).length < 2 ^ (prefixWord ++ tailWord_4782484).sum := by decide
  have hdescent : baseEnd_4782484 < baseStart_4782484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4782484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4782496 : List Nat := [2, 1, 1, 4, 1, 3, 1, 2, 2, 6]
def baseStart_4782496 : Nat := 118140960795 + 4782496 * 2 ^ 59
def prefixEnd_4782496 : Nat := 4983230072969 + 3 ^ 40 * 4782496 * 2
def baseEnd_4782496 : Nat := 818573058735008565368569

theorem tailTrace_4782496 : CollatzResearch.WordTrace tailWord_4782496 prefixEnd_4782496 818573058735008565368569 := by
  unfold tailWord_4782496
  simp only [CollatzResearch.WordTrace]
  refine ⟨87215979640920626067155671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116287972854560834756207561 87215979640920626067155671)
  ·
    refine ⟨130823969461380939100733507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87215979640920626067155671 130823969461380939100733507)
    ·
      refine ⟨196235954192071408651100261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130823969461380939100733507 196235954192071408651100261)
      ·
        refine ⟨36794241411013389122081299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 196235954192071408651100261 36794241411013389122081299)
        ·
          refine ⟨55191362116520083683121949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36794241411013389122081299 55191362116520083683121949)
          ·
            refine ⟨20696760793695031381170731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55191362116520083683121949 20696760793695031381170731)
            ·
              refine ⟨31045141190542547071756097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20696760793695031381170731 31045141190542547071756097)
              ·
                refine ⟨23283855892906910303817073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31045141190542547071756097 23283855892906910303817073)
                ·
                  refine ⟨17462891919680182727862805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23283855892906910303817073 17462891919680182727862805)
                  ·
                    refine ⟨818573058735008565368569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17462891919680182727862805 818573058735008565368569)
                    ·
                      rfl

theorem cell23_4782496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 2, 6].length) (baseStart_4782496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4782496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4782496 prefixEnd_4782496 := by exact prefixLift 4782496
  have htrace : WordTrace (prefixWord ++ tailWord_4782496) baseStart_4782496 baseEnd_4782496 := by
    simpa [prefixWord, tailWord_4782496, baseEnd_4782496] using wordTrace_append hprefix tailTrace_4782496
  have hstable : (prefixWord ++ tailWord_4782496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4782496).length < 2 ^ (prefixWord ++ tailWord_4782496).sum := by decide
  have hdescent : baseEnd_4782496 < baseStart_4782496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4782496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4782497 : List Nat := [1, 2, 3, 5, 1, 1, 1, 1, 4, 1, 3]
def baseStart_4782497 : Nat := 118140960795 + 4782497 * 2 ^ 59
def prefixEnd_4782497 : Nat := 4983230072969 + 3 ^ 40 * 4782497 * 2
def baseEnd_4782497 : Nat := 2455719689685680192193203

theorem tailTrace_4782497 : CollatzResearch.WordTrace tailWord_4782497 prefixEnd_4782497 2455719689685680192193203 := by
  unfold tailWord_4782497
  simp only [CollatzResearch.WordTrace]
  refine ⟨174431995754837629305097745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116287997169891752870065163 174431995754837629305097745)
  ·
    refine ⟨130823996816128221978823309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174431995754837629305097745 130823996816128221978823309)
    ·
      refine ⟨49058998806048083242058741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130823996816128221978823309 49058998806048083242058741)
      ·
        refine ⟨4599281138067007803943007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49058998806048083242058741 4599281138067007803943007)
        ·
          refine ⟨6898921707100511705914511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4599281138067007803943007 6898921707100511705914511)
          ·
            refine ⟨10348382560650767558871767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6898921707100511705914511 10348382560650767558871767)
            ·
              refine ⟨15522573840976151338307651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10348382560650767558871767 15522573840976151338307651)
              ·
                refine ⟨23283860761464227007461477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15522573840976151338307651 23283860761464227007461477)
                ·
                  refine ⟨4365723892774542563899027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23283860761464227007461477 4365723892774542563899027)
                  ·
                    refine ⟨6548585839161813845848541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4365723892774542563899027 6548585839161813845848541)
                    ·
                      refine ⟨2455719689685680192193203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6548585839161813845848541 2455719689685680192193203)
                      ·
                        rfl

theorem cell23_4782497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_4782497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4782497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4782497 prefixEnd_4782497 := by exact prefixLift 4782497
  have htrace : WordTrace (prefixWord ++ tailWord_4782497) baseStart_4782497 baseEnd_4782497 := by
    simpa [prefixWord, tailWord_4782497, baseEnd_4782497] using wordTrace_append hprefix tailTrace_4782497
  have hstable : (prefixWord ++ tailWord_4782497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4782497).length < 2 ^ (prefixWord ++ tailWord_4782497).sum := by decide
  have hdescent : baseEnd_4782497 < baseStart_4782497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4782497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4782560 : List Nat := [2, 1, 1, 3, 1, 1, 7, 2, 5]
def baseStart_4782560 : Nat := 118140960795 + 4782560 * 2 ^ 59
def prefixEnd_4782560 : Nat := 4983230072969 + 3 ^ 40 * 4782560 * 2
def baseEnd_4782560 : Nat := 272861337662990382856157

theorem tailTrace_4782560 : CollatzResearch.WordTrace tailWord_4782560 prefixEnd_4782560 272861337662990382856157 := by
  unfold tailWord_4782560
  simp only [CollatzResearch.WordTrace]
  refine ⟨87217146776804695532320567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116289529035739594043094089 87217146776804695532320567)
  ·
    refine ⟨130825720165207043298480851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87217146776804695532320567 130825720165207043298480851)
    ·
      refine ⟨196238580247810564947721277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130825720165207043298480851 196238580247810564947721277)
      ·
        refine ⟨73589467592928961855395479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196238580247810564947721277 73589467592928961855395479)
        ·
          refine ⟨110384201389393442783093219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73589467592928961855395479 110384201389393442783093219)
          ·
            refine ⟨165576302084090164174639829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110384201389393442783093219 165576302084090164174639829)
            ·
              refine ⟨3880694580095863222843121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 165576302084090164174639829 3880694580095863222843121)
              ·
                refine ⟨2910520935071897417132341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3880694580095863222843121 2910520935071897417132341)
                ·
                  refine ⟨272861337662990382856157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2910520935071897417132341 272861337662990382856157)
                  ·
                    rfl

theorem cell23_4782560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 2, 5].length) (baseStart_4782560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4782560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4782560 prefixEnd_4782560 := by exact prefixLift 4782560
  have htrace : WordTrace (prefixWord ++ tailWord_4782560) baseStart_4782560 baseEnd_4782560 := by
    simpa [prefixWord, tailWord_4782560, baseEnd_4782560] using wordTrace_append hprefix tailTrace_4782560
  have hstable : (prefixWord ++ tailWord_4782560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4782560).length < 2 ^ (prefixWord ++ tailWord_4782560).sum := by decide
  have hdescent : baseEnd_4782560 < baseStart_4782560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4782560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4782700 : List Nat := [2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 4]
def baseStart_4782700 : Nat := 118140960795 + 4782700 * 2 ^ 59
def prefixEnd_4782700 : Nat := 4983230072969 + 3 ^ 40 * 4782700 * 2
def baseEnd_4782700 : Nat := 2455823926258542897954769

theorem tailTrace_4782700 : CollatzResearch.WordTrace tailWord_4782700 prefixEnd_4782700 2455823926258542897954769 := by
  unfold tailWord_4782700
  simp only [CollatzResearch.WordTrace]
  refine ⟨87219699886551097487368777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116292933182068129983158369 87219699886551097487368777)
  ·
    refine ⟨65414774914913323115526583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87219699886551097487368777 65414774914913323115526583)
    ·
      refine ⟨98122162372369984673289875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65414774914913323115526583 98122162372369984673289875)
      ·
        refine ⟨147183243558554977009934813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98122162372369984673289875 147183243558554977009934813)
        ·
          refine ⟨55193716334458116378725555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147183243558554977009934813 55193716334458116378725555)
          ·
            refine ⟨82790574501687174568088333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55193716334458116378725555 82790574501687174568088333)
            ·
              refine ⟨31046465438132690463033125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82790574501687174568088333 31046465438132690463033125)
              ·
                refine ⟨5821212269649879461818711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31046465438132690463033125 5821212269649879461818711)
                ·
                  refine ⟨8731818404474819192728067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5821212269649879461818711 8731818404474819192728067)
                  ·
                    refine ⟨13097727606712228789092101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8731818404474819192728067 13097727606712228789092101)
                    ·
                      refine ⟨2455823926258542897954769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13097727606712228789092101 2455823926258542897954769)
                      ·
                        rfl

theorem cell23_4782700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 4].length) (baseStart_4782700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4782700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4782700 prefixEnd_4782700 := by exact prefixLift 4782700
  have htrace : WordTrace (prefixWord ++ tailWord_4782700) baseStart_4782700 baseEnd_4782700 := by
    simpa [prefixWord, tailWord_4782700, baseEnd_4782700] using wordTrace_append hprefix tailTrace_4782700
  have hstable : (prefixWord ++ tailWord_4782700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4782700).length < 2 ^ (prefixWord ++ tailWord_4782700).sum := by decide
  have hdescent : baseEnd_4782700 < baseStart_4782700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4782700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4782720 : List Nat := [2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 5]
def baseStart_4782720 : Nat := 118140960795 + 4782720 * 2 ^ 59
def prefixEnd_4782720 : Nat := 4983230072969 + 3 ^ 40 * 4782720 * 2
def baseEnd_4782720 : Nat := 2455834195871632819704677

theorem tailTrace_4782720 : CollatzResearch.WordTrace tailWord_4782720 prefixEnd_4782720 2455834195871632819704677 := by
  unfold tailWord_4782720
  simp only [CollatzResearch.WordTrace]
  refine ⟨87220064616514869195232807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116293419488686492260310409 87220064616514869195232807)
  ·
    refine ⟨130830096924772303792849211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87220064616514869195232807 130830096924772303792849211)
    ·
      refine ⟨196245145387158455689273817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130830096924772303792849211 196245145387158455689273817)
      ·
        refine ⟨147183859040368841766955363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196245145387158455689273817 147183859040368841766955363)
        ·
          refine ⟨220775788560553262650433045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147183859040368841766955363 220775788560553262650433045)
          ·
            refine ⟨10348865088775934186739049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 220775788560553262650433045 10348865088775934186739049)
            ·
              refine ⟨7761648816581950640054287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10348865088775934186739049 7761648816581950640054287)
              ·
                refine ⟨11642473224872925960081431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7761648816581950640054287 11642473224872925960081431)
                ·
                  refine ⟨17463709837309388940122147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11642473224872925960081431 17463709837309388940122147)
                  ·
                    refine ⟨26195564755964083410183221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17463709837309388940122147 26195564755964083410183221)
                    ·
                      refine ⟨2455834195871632819704677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26195564755964083410183221 2455834195871632819704677)
                      ·
                        rfl

theorem cell23_4782720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 5].length) (baseStart_4782720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4782720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4782720 prefixEnd_4782720 := by exact prefixLift 4782720
  have htrace : WordTrace (prefixWord ++ tailWord_4782720) baseStart_4782720 baseEnd_4782720 := by
    simpa [prefixWord, tailWord_4782720, baseEnd_4782720] using wordTrace_append hprefix tailTrace_4782720
  have hstable : (prefixWord ++ tailWord_4782720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4782720).length < 2 ^ (prefixWord ++ tailWord_4782720).sum := by decide
  have hdescent : baseEnd_4782720 < baseStart_4782720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4782720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4782740 : List Nat := [2, 4, 2, 2, 1, 1, 1, 10]
def baseStart_4782740 : Nat := 118140960795 + 4782740 * 2 ^ 59
def prefixEnd_4782740 : Nat := 4983230072969 + 3 ^ 40 * 4782740 * 2
def baseEnd_4782740 : Nat := 90957202425360101535355

theorem tailTrace_4782740 : CollatzResearch.WordTrace tailWord_4782740 prefixEnd_4782740 90957202425360101535355 := by
  unfold tailWord_4782740
  simp only [CollatzResearch.WordTrace]
  refine ⟨87220429346478640903096837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116293905795304854537462449 87220429346478640903096837)
  ·
    refine ⟨16353830502464745169330657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87220429346478640903096837 16353830502464745169330657)
    ·
      refine ⟨12265372876848558876997993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16353830502464745169330657 12265372876848558876997993)
      ·
        refine ⟨9199029657636419157748495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12265372876848558876997993 9199029657636419157748495)
        ·
          refine ⟨13798544486454628736622743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9199029657636419157748495 13798544486454628736622743)
          ·
            refine ⟨20697816729681943104934115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13798544486454628736622743 20697816729681943104934115)
            ·
              refine ⟨31046725094522914657401173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20697816729681943104934115 31046725094522914657401173)
              ·
                refine ⟨90957202425360101535355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 31046725094522914657401173 90957202425360101535355)
                ·
                  rfl

theorem cell23_4782740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 10].length) (baseStart_4782740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4782740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4782740 prefixEnd_4782740 := by exact prefixLift 4782740
  have htrace : WordTrace (prefixWord ++ tailWord_4782740) baseStart_4782740 baseEnd_4782740 := by
    simpa [prefixWord, tailWord_4782740, baseEnd_4782740] using wordTrace_append hprefix tailTrace_4782740
  have hstable : (prefixWord ++ tailWord_4782740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4782740).length < 2 ^ (prefixWord ++ tailWord_4782740).sum := by decide
  have hdescent : baseEnd_4782740 < baseStart_4782740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4782740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4782743 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 6]
def baseStart_4782743 : Nat := 118140960795 + 4782743 * 2 ^ 59
def prefixEnd_4782743 : Nat := 4983230072969 + 3 ^ 40 * 4782743 * 2
def baseEnd_4782743 : Nat := 2455846005926686229717071

theorem tailTrace_4782743 : CollatzResearch.WordTrace tailWord_4782743 prefixEnd_4782743 2455846005926686229717071 := by
  unfold tailWord_4782743
  simp only [CollatzResearch.WordTrace]
  refine ⟨174440968111946413318552883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116293978741297608879035255 174440968111946413318552883)
  ·
    refine ⟨261661452167919619977829325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174440968111946413318552883 261661452167919619977829325)
    ·
      refine ⟨98123044562969857491685997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 261661452167919619977829325 98123044562969857491685997)
      ·
        refine ⟨36796141711113696559382249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98123044562969857491685997 36796141711113696559382249)
        ·
          refine ⟨27597106283335272419536687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36796141711113696559382249 27597106283335272419536687)
          ·
            refine ⟨41395659425002908629305031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27597106283335272419536687 41395659425002908629305031)
            ·
              refine ⟨62093489137504362943957547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41395659425002908629305031 62093489137504362943957547)
              ·
                refine ⟨93140233706256544415936321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62093489137504362943957547 93140233706256544415936321)
                ·
                  refine ⟨69855175279692408311952241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93140233706256544415936321 69855175279692408311952241)
                  ·
                    refine ⟨52391381459769306233964181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 69855175279692408311952241 52391381459769306233964181)
                    ·
                      refine ⟨2455846005926686229717071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52391381459769306233964181 2455846005926686229717071)
                      ·
                        rfl

theorem cell23_4782743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_4782743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4782743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4782743 prefixEnd_4782743 := by exact prefixLift 4782743
  have htrace : WordTrace (prefixWord ++ tailWord_4782743) baseStart_4782743 baseEnd_4782743 := by
    simpa [prefixWord, tailWord_4782743, baseEnd_4782743] using wordTrace_append hprefix tailTrace_4782743
  have hstable : (prefixWord ++ tailWord_4782743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4782743).length < 2 ^ (prefixWord ++ tailWord_4782743).sum := by decide
  have hdescent : baseEnd_4782743 < baseStart_4782743 := by decide
  rcases family_descends (prefixWord ++ tailWord_4782743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4782784 : List Nat := [2, 1, 1, 2, 4, 3, 2, 2, 2, 1, 3]
def baseStart_4782784 : Nat := 118140960795 + 4782784 * 2 ^ 59
def prefixEnd_4782784 : Nat := 4983230072969 + 3 ^ 40 * 4782784 * 2
def baseEnd_4782784 : Nat := 2455867058633520569304383

theorem tailTrace_4782784 : CollatzResearch.WordTrace tailWord_4782784 prefixEnd_4782784 2455867058633520569304383 := by
  unfold tailWord_4782784
  simp only [CollatzResearch.WordTrace]
  refine ⟨87221231752398938660397703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116294975669865251547196937 87221231752398938660397703)
  ·
    refine ⟨130831847628598407990596555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87221231752398938660397703 130831847628598407990596555)
    ·
      refine ⟨196247771442897611985894833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130831847628598407990596555 196247771442897611985894833)
      ·
        refine ⟨147185828582173208989421125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196247771442897611985894833 147185828582173208989421125)
        ·
          refine ⟨27597342859157476685516461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147185828582173208989421125 27597342859157476685516461)
          ·
            refine ⟨10349003572184053757068673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27597342859157476685516461 10349003572184053757068673)
            ·
              refine ⟨7761752679138040317801505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10349003572184053757068673 7761752679138040317801505)
              ·
                refine ⟨5821314509353530238351129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7761752679138040317801505 5821314509353530238351129)
                ·
                  refine ⟨4365985882015147678763347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5821314509353530238351129 4365985882015147678763347)
                  ·
                    refine ⟨6548978823022721518145021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4365985882015147678763347 6548978823022721518145021)
                    ·
                      refine ⟨2455867058633520569304383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6548978823022721518145021 2455867058633520569304383)
                      ·
                        rfl

theorem cell23_4782784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2, 2, 1, 3].length) (baseStart_4782784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4782784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4782784 prefixEnd_4782784 := by exact prefixLift 4782784
  have htrace : WordTrace (prefixWord ++ tailWord_4782784) baseStart_4782784 baseEnd_4782784 := by
    simpa [prefixWord, tailWord_4782784, baseEnd_4782784] using wordTrace_append hprefix tailTrace_4782784
  have hstable : (prefixWord ++ tailWord_4782784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4782784).length < 2 ^ (prefixWord ++ tailWord_4782784).sum := by decide
  have hdescent : baseEnd_4782784 < baseStart_4782784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4782784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4782785 : List Nat := [1, 2, 6, 2, 1, 1, 1, 4, 1, 2, 2]
def baseStart_4782785 : Nat := 118140960795 + 4782785 * 2 ^ 59
def prefixEnd_4782785 : Nat := 4983230072969 + 3 ^ 40 * 4782785 * 2
def baseEnd_4782785 : Nat := 2455867572114175065391879

theorem tailTrace_4782785 : CollatzResearch.WordTrace tailWord_4782785 prefixEnd_4782785 2455867572114175065391879 := by
  unfold tailWord_4782785
  simp only [CollatzResearch.WordTrace]
  refine ⟨174442499977794254491581809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116294999985196169661054539 174442499977794254491581809)
  ·
    refine ⟨130831874983345690868686357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174442499977794254491581809 130831874983345690868686357)
    ·
      refine ⟨6132744139844329259469673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 130831874983345690868686357 6132744139844329259469673)
      ·
        refine ⟨4599558104883246944602255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6132744139844329259469673 4599558104883246944602255)
        ·
          refine ⟨6899337157324870416903383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4599558104883246944602255 6899337157324870416903383)
          ·
            refine ⟨10349005735987305625355075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6899337157324870416903383 10349005735987305625355075)
            ·
              refine ⟨15523508603980958438032613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10349005735987305625355075 15523508603980958438032613)
              ·
                refine ⟨2910657863246429707131115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15523508603980958438032613 2910657863246429707131115)
                ·
                  refine ⟨4365986794869644560696673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2910657863246429707131115 4365986794869644560696673)
                  ·
                    refine ⟨3274490096152233420522505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4365986794869644560696673 3274490096152233420522505)
                    ·
                      refine ⟨2455867572114175065391879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3274490096152233420522505 2455867572114175065391879)
                      ·
                        rfl

theorem cell23_4782785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_4782785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4782785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4782785 prefixEnd_4782785 := by exact prefixLift 4782785
  have htrace : WordTrace (prefixWord ++ tailWord_4782785) baseStart_4782785 baseEnd_4782785 := by
    simpa [prefixWord, tailWord_4782785, baseEnd_4782785] using wordTrace_append hprefix tailTrace_4782785
  have hstable : (prefixWord ++ tailWord_4782785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4782785).length < 2 ^ (prefixWord ++ tailWord_4782785).sum := by decide
  have hdescent : baseEnd_4782785 < baseStart_4782785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4782785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4782807 : List Nat := [1, 1, 3, 2, 1, 4, 1, 3, 1, 4, 2]
def baseStart_4782807 : Nat := 118140960795 + 4782807 * 2 ^ 59
def prefixEnd_4782807 : Nat := 4983230072969 + 3 ^ 40 * 4782807 * 2
def baseEnd_4782807 : Nat := 2455878868688573979316777

theorem tailTrace_4782807 : CollatzResearch.WordTrace tailWord_4782807 prefixEnd_4782807 2455878868688573979316777 := by
  unfold tailWord_4782807
  simp only [CollatzResearch.WordTrace]
  refine ⟨174443302383714552248882675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116295534922476368165921783 174443302383714552248882675)
  ·
    refine ⟨261664953575571828373324013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174443302383714552248882675 261664953575571828373324013)
    ·
      refine ⟨98124357590839435639996505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 261664953575571828373324013 98124357590839435639996505)
      ·
        refine ⟨73593268193129576729997379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98124357590839435639996505 73593268193129576729997379)
        ·
          refine ⟨110389902289694365094996069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73593268193129576729997379 110389902289694365094996069)
          ·
            refine ⟨20698106679317693455311763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110389902289694365094996069 20698106679317693455311763)
            ·
              refine ⟨31047160018976540182967645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20698106679317693455311763 31047160018976540182967645)
              ·
                refine ⟨11642685007116202568612867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31047160018976540182967645 11642685007116202568612867)
                ·
                  refine ⟨17464027510674303852919301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11642685007116202568612867 17464027510674303852919301)
                  ·
                    refine ⟨3274505158251431972422369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17464027510674303852919301 3274505158251431972422369)
                    ·
                      refine ⟨2455878868688573979316777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3274505158251431972422369 2455878868688573979316777)
                      ·
                        rfl

theorem cell23_4782807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 4, 2].length) (baseStart_4782807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4782807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4782807 prefixEnd_4782807 := by exact prefixLift 4782807
  have htrace : WordTrace (prefixWord ++ tailWord_4782807) baseStart_4782807 baseEnd_4782807 := by
    simpa [prefixWord, tailWord_4782807, baseEnd_4782807] using wordTrace_append hprefix tailTrace_4782807
  have hstable : (prefixWord ++ tailWord_4782807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4782807).length < 2 ^ (prefixWord ++ tailWord_4782807).sum := by decide
  have hdescent : baseEnd_4782807 < baseStart_4782807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4782807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4782810 : List Nat := [3, 1, 1, 2, 2, 2, 1, 2, 2, 4, 3]
def baseStart_4782810 : Nat := 118140960795 + 4782810 * 2 ^ 59
def prefixEnd_4782810 : Nat := 4983230072969 + 3 ^ 40 * 4782810 * 2
def baseEnd_4782810 : Nat := 2455880409130537467579263

theorem tailTrace_4782810 : CollatzResearch.WordTrace tailWord_4782810 prefixEnd_4782810 2455880409130537467579263 := by
  unfold tailWord_4782810
  simp only [CollatzResearch.WordTrace]
  refine ⟨43610852950675920940310471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116295607868469122507494589 43610852950675920940310471)
  ·
    refine ⟨65416279426013881410465707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43610852950675920940310471 65416279426013881410465707)
    ·
      refine ⟨98124419139020822115698561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65416279426013881410465707 98124419139020822115698561)
      ·
        refine ⟨73593314354265616586773921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98124419139020822115698561 73593314354265616586773921)
        ·
          refine ⟨55194985765699212440080441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73593314354265616586773921 55194985765699212440080441)
          ·
            refine ⟨41396239324274409330060331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55194985765699212440080441 41396239324274409330060331)
            ·
              refine ⟨62094358986411613995090497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41396239324274409330060331 62094358986411613995090497)
              ·
                refine ⟨46570769239808710496317873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62094358986411613995090497 46570769239808710496317873)
                ·
                  refine ⟨34928076929856532872238405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46570769239808710496317873 34928076929856532872238405)
                  ·
                    refine ⟨6549014424348099913544701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34928076929856532872238405 6549014424348099913544701)
                    ·
                      refine ⟨2455880409130537467579263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6549014424348099913544701 2455880409130537467579263)
                      ·
                        rfl

theorem cell23_4782810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 2, 4, 3].length) (baseStart_4782810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4782810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4782810 prefixEnd_4782810 := by exact prefixLift 4782810
  have htrace : WordTrace (prefixWord ++ tailWord_4782810) baseStart_4782810 baseEnd_4782810 := by
    simpa [prefixWord, tailWord_4782810, baseEnd_4782810] using wordTrace_append hprefix tailTrace_4782810
  have hstable : (prefixWord ++ tailWord_4782810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4782810).length < 2 ^ (prefixWord ++ tailWord_4782810).sum := by decide
  have hdescent : baseEnd_4782810 < baseStart_4782810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4782810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4782840 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 4, 3, 3]
def baseStart_4782840 : Nat := 118140960795 + 4782840 * 2 ^ 59
def prefixEnd_4782840 : Nat := 4983230072969 + 3 ^ 40 * 4782840 * 2
def baseEnd_4782840 : Nat := 2455895813550172350204125

theorem tailTrace_4782840 : CollatzResearch.WordTrace tailWord_4782840 prefixEnd_4782840 2455895813550172350204125 := by
  unfold tailWord_4782840
  simp only [CollatzResearch.WordTrace]
  refine ⟨87222252996297499442416987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116296337328396665923222649 87222252996297499442416987)
  ·
    refine ⟨130833379494446249163625481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87222252996297499442416987 130833379494446249163625481)
    ·
      refine ⟨98125034620834686872719111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130833379494446249163625481 98125034620834686872719111)
      ·
        refine ⟨147187551931252030309078667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98125034620834686872719111 147187551931252030309078667)
        ·
          refine ⟨220781327896878045463618001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147187551931252030309078667 220781327896878045463618001)
          ·
            refine ⟨165585995922658534097713501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220781327896878045463618001 165585995922658534097713501)
            ·
              refine ⟨62094748470996950286642563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 165585995922658534097713501 62094748470996950286642563)
              ·
                refine ⟨93142122706495425429963845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62094748470996950286642563 93142122706495425429963845)
                ·
                  refine ⟨17464148007467892268118221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93142122706495425429963845 17464148007467892268118221)
                  ·
                    refine ⟨6549055502800459600544333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17464148007467892268118221 6549055502800459600544333)
                    ·
                      refine ⟨2455895813550172350204125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6549055502800459600544333 2455895813550172350204125)
                      ·
                        rfl

theorem cell23_4782840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 4, 3, 3].length) (baseStart_4782840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4782840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4782840 prefixEnd_4782840 := by exact prefixLift 4782840
  have htrace : WordTrace (prefixWord ++ tailWord_4782840) baseStart_4782840 baseEnd_4782840 := by
    simpa [prefixWord, tailWord_4782840, baseEnd_4782840] using wordTrace_append hprefix tailTrace_4782840
  have hstable : (prefixWord ++ tailWord_4782840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4782840).length < 2 ^ (prefixWord ++ tailWord_4782840).sum := by decide
  have hdescent : baseEnd_4782840 < baseStart_4782840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4782840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4782894 : List Nat := [4, 1, 3, 2, 1, 2, 1, 2, 2, 5]
def baseStart_4782894 : Nat := 118140960795 + 4782894 * 2 ^ 59
def prefixEnd_4782894 : Nat := 4983230072969 + 3 ^ 40 * 4782894 * 2
def baseEnd_4782894 : Nat := 818641180501838379642959

theorem tailTrace_4782894 : CollatzResearch.WordTrace tailWord_4782894 prefixEnd_4782894 818641180501838379642959 := by
  unfold tailWord_4782894
  simp only [CollatzResearch.WordTrace]
  refine ⟨21805809441799920763412467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116297650356266244071533157 21805809441799920763412467)
  ·
    refine ⟨32708714162699881145118701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21805809441799920763412467 32708714162699881145118701)
    ·
      refine ⟨12265767811012455429419513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32708714162699881145118701 12265767811012455429419513)
      ·
        refine ⟨9199325858259341572064635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12265767811012455429419513 9199325858259341572064635)
        ·
          refine ⟨13798988787389012358096953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9199325858259341572064635 13798988787389012358096953)
          ·
            refine ⟨10349241590541759268572715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13798988787389012358096953 10349241590541759268572715)
            ·
              refine ⟨15523862385812638902859073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10349241590541759268572715 15523862385812638902859073)
              ·
                refine ⟨11642896789359479177144305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15523862385812638902859073 11642896789359479177144305)
                ·
                  refine ⟨8732172592019609382858229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11642896789359479177144305 8732172592019609382858229)
                  ·
                    refine ⟨818641180501838379642959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8732172592019609382858229 818641180501838379642959)
                    ·
                      rfl

theorem cell23_4782894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_4782894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4782894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4782894 prefixEnd_4782894 := by exact prefixLift 4782894
  have htrace : WordTrace (prefixWord ++ tailWord_4782894) baseStart_4782894 baseEnd_4782894 := by
    simpa [prefixWord, tailWord_4782894, baseEnd_4782894] using wordTrace_append hprefix tailTrace_4782894
  have hstable : (prefixWord ++ tailWord_4782894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4782894).length < 2 ^ (prefixWord ++ tailWord_4782894).sum := by decide
  have hdescent : baseEnd_4782894 < baseStart_4782894 := by decide
  rcases family_descends (prefixWord ++ tailWord_4782894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4782897 : List Nat := [1, 2, 2, 3, 2, 1, 3, 2, 2, 1, 4]
def baseStart_4782897 : Nat := 118140960795 + 4782897 * 2 ^ 59
def prefixEnd_4782897 : Nat := 4983230072969 + 3 ^ 40 * 4782897 * 2
def baseEnd_4782897 : Nat := 2455925081947478627191363

theorem tailTrace_4782897 : CollatzResearch.WordTrace tailWord_4782897 prefixEnd_4782897 2455925081947478627191363 := by
  unfold tailWord_4782897
  simp only [CollatzResearch.WordTrace]
  refine ⟨174446584953388497619658945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116297723302258998413105963 174446584953388497619658945)
  ·
    refine ⟨130834938715041373214744209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174446584953388497619658945 130834938715041373214744209)
    ·
      refine ⟨98126204036281029911058157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130834938715041373214744209 98126204036281029911058157)
      ·
        refine ⟨36797326513605386216646809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98126204036281029911058157 36797326513605386216646809)
        ·
          refine ⟨27597994885204039662485107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36797326513605386216646809 27597994885204039662485107)
          ·
            refine ⟨41396992327806059493727661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27597994885204039662485107 41396992327806059493727661)
            ·
              refine ⟨15523872122927272310147873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41396992327806059493727661 15523872122927272310147873)
              ·
                refine ⟨11642904092195454232610905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15523872122927272310147873 11642904092195454232610905)
                ·
                  refine ⟨8732178069146590674458179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11642904092195454232610905 8732178069146590674458179)
                  ·
                    refine ⟨13098267103719886011687269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8732178069146590674458179 13098267103719886011687269)
                    ·
                      refine ⟨2455925081947478627191363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13098267103719886011687269 2455925081947478627191363)
                      ·
                        rfl

theorem cell23_4782897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_4782897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4782897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4782897 prefixEnd_4782897 := by exact prefixLift 4782897
  have htrace : WordTrace (prefixWord ++ tailWord_4782897) baseStart_4782897 baseEnd_4782897 := by
    simpa [prefixWord, tailWord_4782897, baseEnd_4782897] using wordTrace_append hprefix tailTrace_4782897
  have hstable : (prefixWord ++ tailWord_4782897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4782897).length < 2 ^ (prefixWord ++ tailWord_4782897).sum := by decide
  have hdescent : baseEnd_4782897 < baseStart_4782897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4782897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4782958 : List Nat := [4, 1, 2, 3, 2, 1, 1, 4, 1, 4]
def baseStart_4782958 : Nat := 118140960795 + 4782958 * 2 ^ 59
def prefixEnd_4782958 : Nat := 4983230072969 + 3 ^ 40 * 4782958 * 2
def baseEnd_4782958 : Nat := 818652134755800962842861

theorem tailTrace_4782958 : CollatzResearch.WordTrace tailWord_4782958 prefixEnd_4782958 818652134755800962842861 := by
  unfold tailWord_4782958
  simp only [CollatzResearch.WordTrace]
  refine ⟨21806101225770938129703691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116299206537445003358419685 21806101225770938129703691)
  ·
    refine ⟨32709151838656407194555537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21806101225770938129703691 32709151838656407194555537)
    ·
      refine ⟨24531863878992305395916653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32709151838656407194555537 24531863878992305395916653)
      ·
        refine ⟨9199448954622114523468745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24531863878992305395916653 9199448954622114523468745)
        ·
          refine ⟨6899586715966585892601559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9199448954622114523468745 6899586715966585892601559)
          ·
            refine ⟨10349380073949878838902339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6899586715966585892601559 10349380073949878838902339)
            ·
              refine ⟨15524070110924818258353509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10349380073949878838902339 15524070110924818258353509)
              ·
                refine ⟨2910763145798403423441283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15524070110924818258353509 2910763145798403423441283)
                ·
                  refine ⟨4366144718697605135161925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2910763145798403423441283 4366144718697605135161925)
                  ·
                    refine ⟨818652134755800962842861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4366144718697605135161925 818652134755800962842861)
                    ·
                      rfl

theorem cell23_4782958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_4782958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4782958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4782958 prefixEnd_4782958 := by exact prefixLift 4782958
  have htrace : WordTrace (prefixWord ++ tailWord_4782958) baseStart_4782958 baseEnd_4782958 := by
    simpa [prefixWord, tailWord_4782958, baseEnd_4782958] using wordTrace_append hprefix tailTrace_4782958
  have hstable : (prefixWord ++ tailWord_4782958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4782958).length < 2 ^ (prefixWord ++ tailWord_4782958).sum := by decide
  have hdescent : baseEnd_4782958 < baseStart_4782958 := by decide
  rcases family_descends (prefixWord ++ tailWord_4782958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4782987 : List Nat := [1, 1, 1, 1, 4, 2, 4, 1, 3, 1, 4]
def baseStart_4782987 : Nat := 118140960795 + 4782987 * 2 ^ 59
def prefixEnd_4782987 : Nat := 4983230072969 + 3 ^ 40 * 4782987 * 2
def baseEnd_4782987 : Nat := 2455971295206383275065949

theorem tailTrace_4782987 : CollatzResearch.WordTrace tailWord_4782987 prefixEnd_4782987 2455971295206383275065949 := by
  unfold tailWord_4782987
  simp only [CollatzResearch.WordTrace]
  refine ⟨174449867523062442990435215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116299911682041628660290143 174449867523062442990435215)
  ·
    refine ⟨261674801284593664485652823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174449867523062442990435215 261674801284593664485652823)
    ·
      refine ⟨392512201926890496728479235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261674801284593664485652823 392512201926890496728479235)
      ·
        refine ⟨588768302890335745092718853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 392512201926890496728479235 588768302890335745092718853)
        ·
          refine ⟨110394056791937952204884785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 588768302890335745092718853 110394056791937952204884785)
          ·
            refine ⟨82795542593953464153663589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110394056791937952204884785 82795542593953464153663589)
            ·
              refine ⟨15524164236366274528811923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82795542593953464153663589 15524164236366274528811923)
              ·
                refine ⟨23286246354549411793217885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15524164236366274528811923 23286246354549411793217885)
                ·
                  refine ⟨8732342382956029422456707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23286246354549411793217885 8732342382956029422456707)
                  ·
                    refine ⟨13098513574434044133685061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8732342382956029422456707 13098513574434044133685061)
                    ·
                      refine ⟨2455971295206383275065949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13098513574434044133685061 2455971295206383275065949)
                      ·
                        rfl

theorem cell23_4782987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3, 1, 4].length) (baseStart_4782987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4782987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4782987 prefixEnd_4782987 := by exact prefixLift 4782987
  have htrace : WordTrace (prefixWord ++ tailWord_4782987) baseStart_4782987 baseEnd_4782987 := by
    simpa [prefixWord, tailWord_4782987, baseEnd_4782987] using wordTrace_append hprefix tailTrace_4782987
  have hstable : (prefixWord ++ tailWord_4782987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4782987).length < 2 ^ (prefixWord ++ tailWord_4782987).sum := by decide
  have hdescent : baseEnd_4782987 < baseStart_4782987 := by decide
  rcases family_descends (prefixWord ++ tailWord_4782987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4782997 : List Nat := [1, 3, 2, 1, 1, 4, 2, 2, 1, 6]
def baseStart_4782997 : Nat := 118140960795 + 4782997 * 2 ^ 59
def prefixEnd_4782997 : Nat := 4983230072969 + 3 ^ 40 * 4782997 * 2
def baseEnd_4782997 : Nat := 818658810004309411980301

theorem tailTrace_4782997 : CollatzResearch.WordTrace tailWord_4782997 prefixEnd_4782997 818658810004309411980301 := by
  unfold tailWord_4782997
  simp only [CollatzResearch.WordTrace]
  refine ⟨174450232253026214698299245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116300154835350809798866163 174450232253026214698299245)
  ·
    refine ⟨65418837094884830511862217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174450232253026214698299245 65418837094884830511862217)
    ·
      refine ⟨49064127821163622883896663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65418837094884830511862217 49064127821163622883896663)
      ·
        refine ⟨73596191731745434325844995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49064127821163622883896663 73596191731745434325844995)
        ·
          refine ⟨110394287597618151488767493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73596191731745434325844995 110394287597618151488767493)
          ·
            refine ⟨20698928924553403404143905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110394287597618151488767493 20698928924553403404143905)
            ·
              refine ⟨15524196693415052553107929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20698928924553403404143905 15524196693415052553107929)
              ·
                refine ⟨11643147520061289414830947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15524196693415052553107929 11643147520061289414830947)
                ·
                  refine ⟨17464721280091934122246421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11643147520061289414830947 17464721280091934122246421)
                  ·
                    refine ⟨818658810004309411980301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17464721280091934122246421 818658810004309411980301)
                    ·
                      rfl

theorem cell23_4782997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_4782997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4782997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4782997 prefixEnd_4782997 := by exact prefixLift 4782997
  have htrace : WordTrace (prefixWord ++ tailWord_4782997) baseStart_4782997 baseEnd_4782997 := by
    simpa [prefixWord, tailWord_4782997, baseEnd_4782997] using wordTrace_append hprefix tailTrace_4782997
  have hstable : (prefixWord ++ tailWord_4782997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4782997).length < 2 ^ (prefixWord ++ tailWord_4782997).sum := by decide
  have hdescent : baseEnd_4782997 < baseStart_4782997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4782997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783055 : List Nat := [1, 1, 2, 1, 1, 8, 1, 3, 1, 2, 2]
def baseStart_4783055 : Nat := 118140960795 + 4783055 * 2 ^ 59
def prefixEnd_4783055 : Nat := 4983230072969 + 3 ^ 40 * 4783055 * 2
def baseEnd_4783055 : Nat := 2456006211890889009015637

theorem tailTrace_4783055 : CollatzResearch.WordTrace tailWord_4783055 prefixEnd_4783055 2456006211890889009015637 := by
  unfold tailWord_4783055
  simp only [CollatzResearch.WordTrace]
  refine ⟨174452347686816090603910619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116301565124544060402607079 174452347686816090603910619)
  ·
    refine ⟨261678521530224135905865929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174452347686816090603910619 261678521530224135905865929)
    ·
      refine ⟨196258891147668101929399447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261678521530224135905865929 196258891147668101929399447)
      ·
        refine ⟨294388336721502152894099171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196258891147668101929399447 294388336721502152894099171)
        ·
          refine ⟨441582505082253229341148757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294388336721502152894099171 441582505082253229341148757)
          ·
            refine ⟨5174794981432655031341587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 441582505082253229341148757 5174794981432655031341587)
            ·
              refine ⟨7762192472148982547012381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5174794981432655031341587 7762192472148982547012381)
              ·
                refine ⟨2910822177055868455129643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7762192472148982547012381 2910822177055868455129643)
                ·
                  refine ⟨4366233265583802682694465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2910822177055868455129643 4366233265583802682694465)
                  ·
                    refine ⟨3274674949187852012020849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4366233265583802682694465 3274674949187852012020849)
                    ·
                      refine ⟨2456006211890889009015637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3274674949187852012020849 2456006211890889009015637)
                      ·
                        rfl

theorem cell23_4783055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 3, 1, 2, 2].length) (baseStart_4783055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783055 prefixEnd_4783055 := by exact prefixLift 4783055
  have htrace : WordTrace (prefixWord ++ tailWord_4783055) baseStart_4783055 baseEnd_4783055 := by
    simpa [prefixWord, tailWord_4783055, baseEnd_4783055] using wordTrace_append hprefix tailTrace_4783055
  have hstable : (prefixWord ++ tailWord_4783055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783055).length < 2 ^ (prefixWord ++ tailWord_4783055).sum := by decide
  have hdescent : baseEnd_4783055 < baseStart_4783055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783092 : List Nat := [2, 6, 2, 1, 1, 1, 1, 1, 3, 2, 3]
def baseStart_4783092 : Nat := 118140960795 + 4783092 * 2 ^ 59
def prefixEnd_4783092 : Nat := 4983230072969 + 3 ^ 40 * 4783092 * 2
def baseEnd_4783092 : Nat := 2456025210675105364252967

theorem tailTrace_4783092 : CollatzResearch.WordTrace tailWord_4783092 prefixEnd_4783092 2456025210675105364252967 := by
  unfold tailWord_4783092
  simp only [CollatzResearch.WordTrace]
  refine ⟨87226848593841022961503765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116302464791788030615338353 87226848593841022961503765)
  ·
    refine ⟨4088758527836297951320489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 87226848593841022961503765 4088758527836297951320489)
    ·
      refine ⟨3066568895877223463490367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4088758527836297951320489 3066568895877223463490367)
      ·
        refine ⟨4599853343815835195235551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3066568895877223463490367 4599853343815835195235551)
        ·
          refine ⟨6899780015723752792853327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4599853343815835195235551 6899780015723752792853327)
          ·
            refine ⟨10349670023585629189279991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6899780015723752792853327 10349670023585629189279991)
            ·
              refine ⟨15524505035378443783919987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10349670023585629189279991 15524505035378443783919987)
              ·
                refine ⟨23286757553067665675879981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15524505035378443783919987 23286757553067665675879981)
                ·
                  refine ⟨8732534082400374628454993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23286757553067665675879981 8732534082400374628454993)
                  ·
                    refine ⟨6549400561800280971341245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8732534082400374628454993 6549400561800280971341245)
                    ·
                      refine ⟨2456025210675105364252967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6549400561800280971341245 2456025210675105364252967)
                      ·
                        rfl

theorem cell23_4783092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_4783092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783092 prefixEnd_4783092 := by exact prefixLift 4783092
  have htrace : WordTrace (prefixWord ++ tailWord_4783092) baseStart_4783092 baseEnd_4783092 := by
    simpa [prefixWord, tailWord_4783092, baseEnd_4783092] using wordTrace_append hprefix tailTrace_4783092
  have hstable : (prefixWord ++ tailWord_4783092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783092).length < 2 ^ (prefixWord ++ tailWord_4783092).sum := by decide
  have hdescent : baseEnd_4783092 < baseStart_4783092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783097 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 4, 1, 5]
def baseStart_4783097 : Nat := 118140960795 + 4783097 * 2 ^ 59
def prefixEnd_4783097 : Nat := 4983230072969 + 3 ^ 40 * 4783097 * 2
def baseEnd_4783097 : Nat := 2456027778078377844690443

theorem tailTrace_4783097 : CollatzResearch.WordTrace tailWord_4783097 prefixEnd_4783097 2456027778078377844690443 := by
  unfold tailWord_4783097
  simp only [CollatzResearch.WordTrace]
  refine ⟨174453879552663931776939545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116302586368442621184626363 174453879552663931776939545)
  ·
    refine ⟨130840409664497948832704659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174453879552663931776939545 130840409664497948832704659)
    ·
      refine ⟨196260614496746923249056989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130840409664497948832704659 196260614496746923249056989)
      ·
        refine ⟨73597730436280096218396371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196260614496746923249056989 73597730436280096218396371)
        ·
          refine ⟨110396595654420144327594557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73597730436280096218396371 110396595654420144327594557)
          ·
            refine ⟨41398723370407554122847959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110396595654420144327594557 41398723370407554122847959)
            ·
              refine ⟨62098085055611331184271939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41398723370407554122847959 62098085055611331184271939)
              ·
                refine ⟨93147127583416996776407909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62098085055611331184271939 93147127583416996776407909)
                ·
                  refine ⟨17465086421890686895576483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93147127583416996776407909 17465086421890686895576483)
                  ·
                    refine ⟨26197629632836030343364725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17465086421890686895576483 26197629632836030343364725)
                    ·
                      refine ⟨2456027778078377844690443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26197629632836030343364725 2456027778078377844690443)
                      ·
                        rfl

theorem cell23_4783097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_4783097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783097 prefixEnd_4783097 := by exact prefixLift 4783097
  have htrace : WordTrace (prefixWord ++ tailWord_4783097) baseStart_4783097 baseEnd_4783097 := by
    simpa [prefixWord, tailWord_4783097, baseEnd_4783097] using wordTrace_append hprefix tailTrace_4783097
  have hstable : (prefixWord ++ tailWord_4783097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783097).length < 2 ^ (prefixWord ++ tailWord_4783097).sum := by decide
  have hdescent : baseEnd_4783097 < baseStart_4783097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783107 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 6, 2, 4]
def baseStart_4783107 : Nat := 118140960795 + 4783107 * 2 ^ 59
def prefixEnd_4783107 : Nat := 4983230072969 + 3 ^ 40 * 4783107 * 2
def baseEnd_4783107 : Nat := 2456032912884922805565397

theorem tailTrace_4783107 : CollatzResearch.WordTrace tailWord_4783107 prefixEnd_4783107 2456032912884922805565397 := by
  unfold tailWord_4783107
  simp only [CollatzResearch.WordTrace]
  refine ⟨174454244282627703484803575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116302829521751802323202383 174454244282627703484803575)
  ·
    refine ⟨261681366423941555227205363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174454244282627703484803575 261681366423941555227205363)
    ·
      refine ⟨392522049635912332840808045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261681366423941555227205363 392522049635912332840808045)
      ·
        refine ⟨147195768613467124815303017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 392522049635912332840808045 147195768613467124815303017)
        ·
          refine ⟨110396826460100343611477263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147195768613467124815303017 110396826460100343611477263)
          ·
            refine ⟨165595239690150515417215895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110396826460100343611477263 165595239690150515417215895)
            ·
              refine ⟨248392859535225773125823843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165595239690150515417215895 248392859535225773125823843)
              ·
                refine ⟨372589289302838659688735765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248392859535225773125823843 372589289302838659688735765)
                ·
                  refine ⟨17465122936070562172909489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 372589289302838659688735765 17465122936070562172909489)
                  ·
                    refine ⟨13098842202052921629682117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17465122936070562172909489 13098842202052921629682117)
                    ·
                      refine ⟨2456032912884922805565397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13098842202052921629682117 2456032912884922805565397)
                      ·
                        rfl

theorem cell23_4783107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2, 4].length) (baseStart_4783107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783107 prefixEnd_4783107 := by exact prefixLift 4783107
  have htrace : WordTrace (prefixWord ++ tailWord_4783107) baseStart_4783107 baseEnd_4783107 := by
    simpa [prefixWord, tailWord_4783107, baseEnd_4783107] using wordTrace_append hprefix tailTrace_4783107
  have hstable : (prefixWord ++ tailWord_4783107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783107).length < 2 ^ (prefixWord ++ tailWord_4783107).sum := by decide
  have hdescent : baseEnd_4783107 < baseStart_4783107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783111 : List Nat := [1, 1, 4, 3, 1, 1, 3, 2, 1, 4, 2]
def baseStart_4783111 : Nat := 118140960795 + 4783111 * 2 ^ 59
def prefixEnd_4783111 : Nat := 4983230072969 + 3 ^ 40 * 4783111 * 2
def baseEnd_4783111 : Nat := 2456034966807540789915379

theorem tailTrace_4783111 : CollatzResearch.WordTrace tailWord_4783111 prefixEnd_4783111 2456034966807540789915379 := by
  unfold tailWord_4783111
  simp only [CollatzResearch.WordTrace]
  refine ⟨174454390174613212167949187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116302926783075474778632791 174454390174613212167949187)
  ·
    refine ⟨261681585261919818251923781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174454390174613212167949187 261681585261919818251923781)
    ·
      refine ⟨49065297236609965922235709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 261681585261919818251923781 49065297236609965922235709)
      ·
        refine ⟨18399486463728737220838391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49065297236609965922235709 18399486463728737220838391)
        ·
          refine ⟨27599229695593105831257587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18399486463728737220838391 27599229695593105831257587)
          ·
            refine ⟨41398844543389658746886381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27599229695593105831257587 41398844543389658746886381)
            ·
              refine ⟨15524566703771122030082393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41398844543389658746886381 15524566703771122030082393)
              ·
                refine ⟨11643425027828341522561795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15524566703771122030082393 11643425027828341522561795)
                ·
                  refine ⟨17465137541742512283842693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11643425027828341522561795 17465137541742512283842693)
                  ·
                    refine ⟨3274713289076721053220505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17465137541742512283842693 3274713289076721053220505)
                    ·
                      refine ⟨2456034966807540789915379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3274713289076721053220505 2456034966807540789915379)
                      ·
                        rfl

theorem cell23_4783111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_4783111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783111 prefixEnd_4783111 := by exact prefixLift 4783111
  have htrace : WordTrace (prefixWord ++ tailWord_4783111) baseStart_4783111 baseEnd_4783111 := by
    simpa [prefixWord, tailWord_4783111, baseEnd_4783111] using wordTrace_append hprefix tailTrace_4783111
  have hstable : (prefixWord ++ tailWord_4783111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783111).length < 2 ^ (prefixWord ++ tailWord_4783111).sum := by decide
  have hdescent : baseEnd_4783111 < baseStart_4783111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783114 : List Nat := [3, 1, 2, 2, 3, 1, 2, 1, 2, 1, 5]
def baseStart_4783114 : Nat := 118140960795 + 4783114 * 2 ^ 59
def prefixEnd_4783114 : Nat := 4983230072969 + 3 ^ 40 * 4783114 * 2
def baseEnd_4783114 : Nat := 2456036507249504278177865

theorem tailTrace_4783114 : CollatzResearch.WordTrace tailWord_4783114 prefixEnd_4783114 2456036507249504278177865 := by
  unfold tailWord_4783114
  simp only [CollatzResearch.WordTrace]
  refine ⟨43613624898400585920077099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116302999729068229120205597 43613624898400585920077099)
  ·
    refine ⟨65420437347600878880115649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43613624898400585920077099 65420437347600878880115649)
    ·
      refine ⟨49065328010700659160086737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65420437347600878880115649 49065328010700659160086737)
      ·
        refine ⟨36798996008025494370065053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49065328010700659160086737 36798996008025494370065053)
        ·
          refine ⟨13799623503009560388774395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36798996008025494370065053 13799623503009560388774395)
          ·
            refine ⟨20699435254514340583161593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13799623503009560388774395 20699435254514340583161593)
            ·
              refine ⟨15524576440885755437371195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20699435254514340583161593 15524576440885755437371195)
              ·
                refine ⟨23286864661328633156056793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15524576440885755437371195 23286864661328633156056793)
                ·
                  refine ⟨17465148495996474867042595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23286864661328633156056793 17465148495996474867042595)
                  ·
                    refine ⟨26197722743994712300563893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17465148495996474867042595 26197722743994712300563893)
                    ·
                      refine ⟨2456036507249504278177865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26197722743994712300563893 2456036507249504278177865)
                      ·
                        rfl

theorem cell23_4783114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_4783114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783114 prefixEnd_4783114 := by exact prefixLift 4783114
  have htrace : WordTrace (prefixWord ++ tailWord_4783114) baseStart_4783114 baseEnd_4783114 := by
    simpa [prefixWord, tailWord_4783114, baseEnd_4783114] using wordTrace_append hprefix tailTrace_4783114
  have hstable : (prefixWord ++ tailWord_4783114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783114).length < 2 ^ (prefixWord ++ tailWord_4783114).sum := by decide
  have hdescent : baseEnd_4783114 < baseStart_4783114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783128 : List Nat := [2, 1, 2, 3, 2, 2, 1, 4, 2, 2, 2]
def baseStart_4783128 : Nat := 118140960795 + 4783128 * 2 ^ 59
def prefixEnd_4783128 : Nat := 4983230072969 + 3 ^ 40 * 4783128 * 2
def baseEnd_4783128 : Nat := 2456043695978667223402801

theorem tailTrace_4783128 : CollatzResearch.WordTrace tailWord_4783128 prefixEnd_4783128 2456043695978667223402801 := by
  unfold tailWord_4783128
  simp only [CollatzResearch.WordTrace]
  refine ⟨87227505107775812035659019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116303340143701082714212025 87227505107775812035659019)
  ·
    refine ⟨130841257661663718053488529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87227505107775812035659019 130841257661663718053488529)
    ·
      refine ⟨98130943246247788540116397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130841257661663718053488529 98130943246247788540116397)
      ·
        refine ⟨36799103717342920702543649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98130943246247788540116397 36799103717342920702543649)
        ·
          refine ⟨27599327788007190526907737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36799103717342920702543649 27599327788007190526907737)
          ·
            refine ⟨20699495841005392895180803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27599327788007190526907737 20699495841005392895180803)
            ·
              refine ⟨31049243761508089342771205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20699495841005392895180803 31049243761508089342771205)
              ·
                refine ⟨5821733205282766751769601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31049243761508089342771205 5821733205282766751769601)
                ·
                  refine ⟨4366299903962075063827201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5821733205282766751769601 4366299903962075063827201)
                  ·
                    refine ⟨3274724927971556297870401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4366299903962075063827201 3274724927971556297870401)
                    ·
                      refine ⟨2456043695978667223402801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3274724927971556297870401 2456043695978667223402801)
                      ·
                        rfl

theorem cell23_4783128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4, 2, 2, 2].length) (baseStart_4783128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783128 prefixEnd_4783128 := by exact prefixLift 4783128
  have htrace : WordTrace (prefixWord ++ tailWord_4783128) baseStart_4783128 baseEnd_4783128 := by
    simpa [prefixWord, tailWord_4783128, baseEnd_4783128] using wordTrace_append hprefix tailTrace_4783128
  have hstable : (prefixWord ++ tailWord_4783128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783128).length < 2 ^ (prefixWord ++ tailWord_4783128).sum := by decide
  have hdescent : baseEnd_4783128 < baseStart_4783128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783147 : List Nat := [1, 1, 1, 1, 2, 1, 6, 2, 1, 7]
def baseStart_4783147 : Nat := 118140960795 + 4783147 * 2 ^ 59
def prefixEnd_4783147 : Nat := 4983230072969 + 3 ^ 40 * 4783147 * 2
def baseEnd_4783147 : Nat := 818684484037034216355071

theorem tailTrace_4783147 : CollatzResearch.WordTrace tailWord_4783147 prefixEnd_4783147 818684484037034216355071 := by
  unfold tailWord_4783147
  simp only [CollatzResearch.WordTrace]
  refine ⟨174455703202482790316259695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116303802134988526877506463 174455703202482790316259695)
  ·
    refine ⟨261683554803724185474389543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174455703202482790316259695 261683554803724185474389543)
    ·
      refine ⟨392525332205586278211584315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261683554803724185474389543 392525332205586278211584315)
      ·
        refine ⟨588787998308379417317376473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 392525332205586278211584315 588787998308379417317376473)
        ·
          refine ⟨441590998731284562988032355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 588787998308379417317376473 441590998731284562988032355)
          ·
            refine ⟨662386498096926844482048533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 441590998731284562988032355 662386498096926844482048533)
            ·
              refine ⟨31049367098293445835096025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 662386498096926844482048533 31049367098293445835096025)
              ·
                refine ⟨23287025323720084376322019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31049367098293445835096025 23287025323720084376322019)
                ·
                  refine ⟨34930537985580126564483029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23287025323720084376322019 34930537985580126564483029)
                  ·
                    refine ⟨818684484037034216355071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34930537985580126564483029 818684484037034216355071)
                    ·
                      rfl

theorem cell23_4783147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 7].length) (baseStart_4783147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783147 prefixEnd_4783147 := by exact prefixLift 4783147
  have htrace : WordTrace (prefixWord ++ tailWord_4783147) baseStart_4783147 baseEnd_4783147 := by
    simpa [prefixWord, tailWord_4783147, baseEnd_4783147] using wordTrace_append hprefix tailTrace_4783147
  have hstable : (prefixWord ++ tailWord_4783147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783147).length < 2 ^ (prefixWord ++ tailWord_4783147).sum := by decide
  have hdescent : baseEnd_4783147 < baseStart_4783147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783164 : List Nat := [2, 2, 2, 2, 2, 3, 1, 1, 1, 7]
def baseStart_4783164 : Nat := 118140960795 + 4783164 * 2 ^ 59
def prefixEnd_4783164 : Nat := 4983230072969 + 3 ^ 40 * 4783164 * 2
def baseEnd_4783164 : Nat := 818687393760743027517545

theorem tailTrace_4783164 : CollatzResearch.WordTrace tailWord_4783164 prefixEnd_4783164 818687393760743027517545 := by
  unfold tailWord_4783164
  simp only [CollatzResearch.WordTrace]
  refine ⟨87228161621710601109814273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116304215495614134813085697 87228161621710601109814273)
  ·
    refine ⟨65421121216282950832360705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87228161621710601109814273 65421121216282950832360705)
    ·
      refine ⟨49065840912212213124270529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65421121216282950832360705 49065840912212213124270529)
      ·
        refine ⟨36799380684159159843202897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49065840912212213124270529 36799380684159159843202897)
        ·
          refine ⟨27599535513119369882402173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36799380684159159843202897 27599535513119369882402173)
          ·
            refine ⟨10349825817419763705900815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27599535513119369882402173 10349825817419763705900815)
            ·
              refine ⟨15524738726129645558851223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10349825817419763705900815 15524738726129645558851223)
              ·
                refine ⟨23287108089194468338276835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15524738726129645558851223 23287108089194468338276835)
                ·
                  refine ⟨34930662133791702507415253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23287108089194468338276835 34930662133791702507415253)
                  ·
                    refine ⟨818687393760743027517545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34930662133791702507415253 818687393760743027517545)
                    ·
                      rfl

theorem cell23_4783164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_4783164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783164 prefixEnd_4783164 := by exact prefixLift 4783164
  have htrace : WordTrace (prefixWord ++ tailWord_4783164) baseStart_4783164 baseEnd_4783164 := by
    simpa [prefixWord, tailWord_4783164, baseEnd_4783164] using wordTrace_append hprefix tailTrace_4783164
  have hstable : (prefixWord ++ tailWord_4783164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783164).length < 2 ^ (prefixWord ++ tailWord_4783164).sum := by decide
  have hdescent : baseEnd_4783164 < baseStart_4783164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783184 : List Nat := [2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 4]
def baseStart_4783184 : Nat := 118140960795 + 4783184 * 2 ^ 59
def prefixEnd_4783184 : Nat := 4983230072969 + 3 ^ 40 * 4783184 * 2
def baseEnd_4783184 : Nat := 2456072450895319004302543

theorem tailTrace_4783184 : CollatzResearch.WordTrace tailWord_4783184 prefixEnd_4783184 2456072450895319004302543 := by
  unfold tailWord_4783184
  simp only [CollatzResearch.WordTrace]
  refine ⟨87228526351674372817678303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116304701802232497090237737 87228526351674372817678303)
  ·
    refine ⟨130842789527511559226517455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87228526351674372817678303 130842789527511559226517455)
    ·
      refine ⟨196264184291267338839776183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130842789527511559226517455 196264184291267338839776183)
      ·
        refine ⟨294396276436901008259664275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196264184291267338839776183 294396276436901008259664275)
        ·
          refine ⟨441594414655351512389496413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294396276436901008259664275 441594414655351512389496413)
          ·
            refine ⟨165597905495756817146061155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 441594414655351512389496413 165597905495756817146061155)
            ·
              refine ⟨248396858243635225719091733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165597905495756817146061155 248396858243635225719091733)
              ·
                refine ⟨11643602730170401205582425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 248396858243635225719091733 11643602730170401205582425)
                ·
                  refine ⟨8732702047627800904186819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11643602730170401205582425 8732702047627800904186819)
                  ·
                    refine ⟨13099053071441701356280229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8732702047627800904186819 13099053071441701356280229)
                    ·
                      refine ⟨2456072450895319004302543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13099053071441701356280229 2456072450895319004302543)
                      ·
                        rfl

theorem cell23_4783184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 4].length) (baseStart_4783184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783184 prefixEnd_4783184 := by exact prefixLift 4783184
  have htrace : WordTrace (prefixWord ++ tailWord_4783184) baseStart_4783184 baseEnd_4783184 := by
    simpa [prefixWord, tailWord_4783184, baseEnd_4783184] using wordTrace_append hprefix tailTrace_4783184
  have hstable : (prefixWord ++ tailWord_4783184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783184).length < 2 ^ (prefixWord ++ tailWord_4783184).sum := by decide
  have hdescent : baseEnd_4783184 < baseStart_4783184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783187 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 5]
def baseStart_4783187 : Nat := 118140960795 + 4783187 * 2 ^ 59
def prefixEnd_4783187 : Nat := 4983230072969 + 3 ^ 40 * 4783187 * 2
def baseEnd_4783187 : Nat := 2456073991337282492565029

theorem tailTrace_4783187 : CollatzResearch.WordTrace tailWord_4783187 prefixEnd_4783187 2456073991337282492565029 := by
  unfold tailWord_4783187
  simp only [CollatzResearch.WordTrace]
  refine ⟨174457162122337877147715815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116304774748225251431810543 174457162122337877147715815)
  ·
    refine ⟨261685743183506815721573723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174457162122337877147715815 261685743183506815721573723)
    ·
      refine ⟨392528614775260223582360585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261685743183506815721573723 392528614775260223582360585)
      ·
        refine ⟨294396461081445167686770439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 392528614775260223582360585 294396461081445167686770439)
        ·
          refine ⟨441594691622167751530155659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294396461081445167686770439 441594691622167751530155659)
          ·
            refine ⟨662392037433251627295233489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 441594691622167751530155659 662392037433251627295233489)
            ·
              refine ⟨496794028074938720471425117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 662392037433251627295233489 496794028074938720471425117)
              ·
                refine ⟨186297760528102020176784419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 496794028074938720471425117 186297760528102020176784419)
                ·
                  refine ⟨279446640792153030265176629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 186297760528102020176784419 279446640792153030265176629)
                  ·
                    refine ⟨26198122574264346587360309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 279446640792153030265176629 26198122574264346587360309)
                    ·
                      refine ⟨2456073991337282492565029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26198122574264346587360309 2456073991337282492565029)
                      ·
                        rfl

theorem cell23_4783187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 5].length) (baseStart_4783187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783187 prefixEnd_4783187 := by exact prefixLift 4783187
  have htrace : WordTrace (prefixWord ++ tailWord_4783187) baseStart_4783187 baseEnd_4783187 := by
    simpa [prefixWord, tailWord_4783187, baseEnd_4783187] using wordTrace_append hprefix tailTrace_4783187
  have hstable : (prefixWord ++ tailWord_4783187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783187).length < 2 ^ (prefixWord ++ tailWord_4783187).sum := by decide
  have hdescent : baseEnd_4783187 < baseStart_4783187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783198 : List Nat := [4, 4, 1, 1, 1, 1, 1, 2, 1, 7]
def baseStart_4783198 : Nat := 118140960795 + 4783198 * 2 ^ 59
def prefixEnd_4783198 : Nat := 4983230072969 + 3 ^ 40 * 4783198 * 2
def baseEnd_4783198 : Nat := 818693213208160649842493

theorem tailTrace_4783198 : CollatzResearch.WordTrace tailWord_4783198 prefixEnd_4783198 818693213208160649842493 := by
  unfold tailWord_4783198
  simp only [CollatzResearch.WordTrace]
  refine ⟨21807195415662253253295781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116305042216865350684244165 21807195415662253253295781)
  ·
    refine ⟨4088849140436672484992959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21807195415662253253295781 4088849140436672484992959)
    ·
      refine ⟨6133273710655008727489439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4088849140436672484992959 6133273710655008727489439)
      ·
        refine ⟨9199910565982513091234159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6133273710655008727489439 9199910565982513091234159)
        ·
          refine ⟨13799865848973769636851239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9199910565982513091234159 13799865848973769636851239)
          ·
            refine ⟨20699798773460654455276859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13799865848973769636851239 20699798773460654455276859)
            ·
              refine ⟨31049698160190981682915289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20699798773460654455276859 31049698160190981682915289)
              ·
                refine ⟨23287273620143236262186467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31049698160190981682915289 23287273620143236262186467)
                ·
                  refine ⟨34930910430214854393279701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23287273620143236262186467 34930910430214854393279701)
                  ·
                    refine ⟨818693213208160649842493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34930910430214854393279701 818693213208160649842493)
                    ·
                      rfl

theorem cell23_4783198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_4783198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783198 prefixEnd_4783198 := by exact prefixLift 4783198
  have htrace : WordTrace (prefixWord ++ tailWord_4783198) baseStart_4783198 baseEnd_4783198 := by
    simpa [prefixWord, tailWord_4783198, baseEnd_4783198] using wordTrace_append hprefix tailTrace_4783198
  have hstable : (prefixWord ++ tailWord_4783198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783198).length < 2 ^ (prefixWord ++ tailWord_4783198).sum := by decide
  have hdescent : baseEnd_4783198 < baseStart_4783198 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783201 : List Nat := [1, 2, 3, 1, 1, 2, 4, 1, 2, 4, 2]
def baseStart_4783201 : Nat := 118140960795 + 4783201 * 2 ^ 59
def prefixEnd_4783201 : Nat := 4983230072969 + 3 ^ 40 * 4783201 * 2
def baseEnd_4783201 : Nat := 2456081180066445437789965

theorem tailTrace_4783201 : CollatzResearch.WordTrace tailWord_4783201 prefixEnd_4783201 2456081180066445437789965 := by
  unfold tailWord_4783201
  simp only [CollatzResearch.WordTrace]
  refine ⟨174457672744287157538725457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116305115162858105025816971 174457672744287157538725457)
  ·
    refine ⟨130843254558215368154044093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174457672744287157538725457 130843254558215368154044093)
    ·
      refine ⟨49066220459330763057766535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130843254558215368154044093 49066220459330763057766535)
      ·
        refine ⟨73599330688996144586649803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49066220459330763057766535 73599330688996144586649803)
        ·
          refine ⟨110398996033494216879974705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73599330688996144586649803 110398996033494216879974705)
          ·
            refine ⟨82799247025120662659981029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110398996033494216879974705 82799247025120662659981029)
            ·
              refine ⟨15524858817210124248746443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82799247025120662659981029 15524858817210124248746443)
              ·
                refine ⟨23287288225815186373119665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15524858817210124248746443 23287288225815186373119665)
                ·
                  refine ⟨17465466169361389779839749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23287288225815186373119665 17465466169361389779839749)
                  ·
                    refine ⟨3274774906755260583719953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17465466169361389779839749 3274774906755260583719953)
                    ·
                      refine ⟨2456081180066445437789965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3274774906755260583719953 2456081180066445437789965)
                      ·
                        rfl

theorem cell23_4783201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 4, 2].length) (baseStart_4783201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783201 prefixEnd_4783201 := by exact prefixLift 4783201
  have htrace : WordTrace (prefixWord ++ tailWord_4783201) baseStart_4783201 baseEnd_4783201 := by
    simpa [prefixWord, tailWord_4783201, baseEnd_4783201] using wordTrace_append hprefix tailTrace_4783201
  have hstable : (prefixWord ++ tailWord_4783201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783201).length < 2 ^ (prefixWord ++ tailWord_4783201).sum := by decide
  have hdescent : baseEnd_4783201 < baseStart_4783201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783258 : List Nat := [3, 1, 1, 5, 1, 1, 4, 1, 6]
def baseStart_4783258 : Nat := 118140960795 + 4783258 * 2 ^ 59
def prefixEnd_4783258 : Nat := 4983230072969 + 3 ^ 40 * 4783258 * 2
def baseEnd_4783258 : Nat := 272901160940416857197467

theorem tailTrace_4783258 : CollatzResearch.WordTrace tailWord_4783258 prefixEnd_4783258 272901160940416857197467 := by
  unfold tailWord_4783258
  simp only [CollatzResearch.WordTrace]
  refine ⟨43614937926270164068387607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116306501136720437515700285 43614937926270164068387607)
  ·
    refine ⟨65422406889405246102581411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43614937926270164068387607 65422406889405246102581411)
    ·
      refine ⟨98133610334107869153872117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65422406889405246102581411 98133610334107869153872117)
      ·
        refine ⟨9200025968822612733175511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 98133610334107869153872117 9200025968822612733175511)
        ·
          refine ⟨13800038953233919099763267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9200025968822612733175511 13800038953233919099763267)
          ·
            refine ⟨20700058429850878649644901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13800038953233919099763267 20700058429850878649644901)
            ·
              refine ⟨3881260955597039746808419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20700058429850878649644901 3881260955597039746808419)
              ·
                refine ⟨5821891433395559620212629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3881260955597039746808419 5821891433395559620212629)
                ·
                  refine ⟨272901160940416857197467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5821891433395559620212629 272901160940416857197467)
                  ·
                    rfl

theorem cell23_4783258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 1, 6].length) (baseStart_4783258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783258 prefixEnd_4783258 := by exact prefixLift 4783258
  have htrace : WordTrace (prefixWord ++ tailWord_4783258) baseStart_4783258 baseEnd_4783258 := by
    simpa [prefixWord, tailWord_4783258, baseEnd_4783258] using wordTrace_append hprefix tailTrace_4783258
  have hstable : (prefixWord ++ tailWord_4783258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783258).length < 2 ^ (prefixWord ++ tailWord_4783258).sum := by decide
  have hdescent : baseEnd_4783258 < baseStart_4783258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783304 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 3, 1, 6]
def baseStart_4783304 : Nat := 118140960795 + 4783304 * 2 ^ 59
def prefixEnd_4783304 : Nat := 4983230072969 + 3 ^ 40 * 4783304 * 2
def baseEnd_4783304 : Nat := 2456134068573858534801991

theorem tailTrace_4783304 : CollatzResearch.WordTrace tailWord_4783304 prefixEnd_4783304 2456134068573858534801991 := by
  unfold tailWord_4783304
  simp only [CollatzResearch.WordTrace]
  refine ⟨87230714731457003064862483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116307619641942670753149977 87230714731457003064862483)
  ·
    refine ⟨130846072097185504597293725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87230714731457003064862483 130846072097185504597293725)
    ·
      refine ⟨49067277036444564223985147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130846072097185504597293725 49067277036444564223985147)
      ·
        refine ⟨73600915554666846335977721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49067277036444564223985147 73600915554666846335977721)
        ·
          refine ⟨55200686666000134751983291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73600915554666846335977721 55200686666000134751983291)
          ·
            refine ⟨82801029999000202127974937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55200686666000134751983291 82801029999000202127974937)
            ·
              refine ⟨62100772499250151595981203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82801029999000202127974937 62100772499250151595981203)
              ·
                refine ⟨93151158748875227393971805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62100772499250151595981203 93151158748875227393971805)
                ·
                  refine ⟨34931684530828210272739427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93151158748875227393971805 34931684530828210272739427)
                  ·
                    refine ⟨52397526796242315409109141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34931684530828210272739427 52397526796242315409109141)
                    ·
                      refine ⟨2456134068573858534801991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52397526796242315409109141 2456134068573858534801991)
                      ·
                        rfl

theorem cell23_4783304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_4783304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783304 prefixEnd_4783304 := by exact prefixLift 4783304
  have htrace : WordTrace (prefixWord ++ tailWord_4783304) baseStart_4783304 baseEnd_4783304 := by
    simpa [prefixWord, tailWord_4783304, baseEnd_4783304] using wordTrace_append hprefix tailTrace_4783304
  have hstable : (prefixWord ++ tailWord_4783304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783304).length < 2 ^ (prefixWord ++ tailWord_4783304).sum := by decide
  have hdescent : baseEnd_4783304 < baseStart_4783304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783342 : List Nat := [4, 1, 2, 1, 1, 1, 3, 5, 1, 2, 2]
def baseStart_4783342 : Nat := 118140960795 + 4783342 * 2 ^ 59
def prefixEnd_4783342 : Nat := 4983230072969 + 3 ^ 40 * 4783342 * 2
def baseEnd_4783342 : Nat := 2456153580838729386126817

theorem tailTrace_4783342 : CollatzResearch.WordTrace tailWord_4783342 prefixEnd_4783342 2456153580838729386126817 := by
  unfold tailWord_4783342
  simp only [CollatzResearch.WordTrace]
  refine ⟨21807851929597042327451035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116308543624517559079738853 21807851929597042327451035)
  ·
    refine ⟨32711777894395563491176553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21807851929597042327451035 32711777894395563491176553)
    ·
      refine ⟨24533833420796672618382415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32711777894395563491176553 24533833420796672618382415)
      ·
        refine ⟨36800750131195008927573623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24533833420796672618382415 36800750131195008927573623)
        ·
          refine ⟨55201125196792513391360435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36800750131195008927573623 55201125196792513391360435)
          ·
            refine ⟨82801687795188770087040653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55201125196792513391360435 82801687795188770087040653)
            ·
              refine ⟨31050632923195788782640245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82801687795188770087040653 31050632923195788782640245)
              ·
                refine ⟨2910996836549605198372523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31050632923195788782640245 2910996836549605198372523)
                ·
                  refine ⟨4366495254824407797558785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2910996836549605198372523 4366495254824407797558785)
                  ·
                    refine ⟨3274871441118305848169089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4366495254824407797558785 3274871441118305848169089)
                    ·
                      refine ⟨2456153580838729386126817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3274871441118305848169089 2456153580838729386126817)
                      ·
                        rfl

theorem cell23_4783342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 5, 1, 2, 2].length) (baseStart_4783342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783342 prefixEnd_4783342 := by exact prefixLift 4783342
  have htrace : WordTrace (prefixWord ++ tailWord_4783342) baseStart_4783342 baseEnd_4783342 := by
    simpa [prefixWord, tailWord_4783342, baseEnd_4783342] using wordTrace_append hprefix tailTrace_4783342
  have hstable : (prefixWord ++ tailWord_4783342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783342).length < 2 ^ (prefixWord ++ tailWord_4783342).sum := by decide
  have hdescent : baseEnd_4783342 < baseStart_4783342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783402 : List Nat := [3, 1, 4, 2, 1, 1, 2, 3, 1, 3, 2]
def baseStart_4783402 : Nat := 118140960795 + 4783402 * 2 ^ 59
def prefixEnd_4783402 : Nat := 4983230072969 + 3 ^ 40 * 4783402 * 2
def baseEnd_4783402 : Nat := 2456184389677999151376541

theorem tailTrace_4783402 : CollatzResearch.WordTrace tailWord_4783402 prefixEnd_4783402 2456184389677999151376541 := by
  unfold tailWord_4783402
  simp only [CollatzResearch.WordTrace]
  refine ⟨43616250954139742216698115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116310002544372645911194973 43616250954139742216698115)
  ·
    refine ⟨65424376431209613325047173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43616250954139742216698115 65424376431209613325047173)
    ·
      refine ⟨12267070580851802498446345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65424376431209613325047173 12267070580851802498446345)
      ·
        refine ⟨9200302935638851873834759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12267070580851802498446345 9200302935638851873834759)
        ·
          refine ⟨13800454403458277810752139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9200302935638851873834759 13800454403458277810752139)
          ·
            refine ⟨20700681605187416716128209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13800454403458277810752139 20700681605187416716128209)
            ·
              refine ⟨15525511203890562537096157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20700681605187416716128209 15525511203890562537096157)
              ·
                refine ⟨5822066701458960951411059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15525511203890562537096157 5822066701458960951411059)
                ·
                  refine ⟨8733100052188441427116589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5822066701458960951411059 8733100052188441427116589)
                  ·
                    refine ⟨3274912519570665535168721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8733100052188441427116589 3274912519570665535168721)
                    ·
                      refine ⟨2456184389677999151376541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3274912519570665535168721 2456184389677999151376541)
                      ·
                        rfl

theorem cell23_4783402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_4783402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783402 prefixEnd_4783402 := by exact prefixLift 4783402
  have htrace : WordTrace (prefixWord ++ tailWord_4783402) baseStart_4783402 baseEnd_4783402 := by
    simpa [prefixWord, tailWord_4783402, baseEnd_4783402] using wordTrace_append hprefix tailTrace_4783402
  have hstable : (prefixWord ++ tailWord_4783402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783402).length < 2 ^ (prefixWord ++ tailWord_4783402).sum := by decide
  have hdescent : baseEnd_4783402 < baseStart_4783402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783453 : List Nat := [1, 4, 5, 1, 1, 1, 3, 1, 1, 3, 2]
def baseStart_4783453 : Nat := 118140960795 + 4783453 * 2 ^ 59
def prefixEnd_4783453 : Nat := 4983230072969 + 3 ^ 40 * 4783453 * 2
def baseEnd_4783453 : Nat := 2456210577191378451838807

theorem tailTrace_4783453 : CollatzResearch.WordTrace tailWord_4783453 prefixEnd_4783453 2456210577191378451838807 := by
  unfold tailWord_4783453
  simp only [CollatzResearch.WordTrace]
  refine ⟨174466863939374204576899013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116311242626249469717932675 174466863939374204576899013)
  ·
    refine ⟨32712536988632663358168565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174466863939374204576899013 32712536988632663358168565)
    ·
      refine ⟨3066800342684312189828303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32712536988632663358168565 3066800342684312189828303)
      ·
        refine ⟨4600200514026468284742455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3066800342684312189828303 4600200514026468284742455)
        ·
          refine ⟨6900300771039702427113683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4600200514026468284742455 6900300771039702427113683)
          ·
            refine ⟨10350451156559553640670525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6900300771039702427113683 10350451156559553640670525)
            ·
              refine ⟨3881419183709832615251447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10350451156559553640670525 3881419183709832615251447)
              ·
                refine ⟨5822128775564748922877171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3881419183709832615251447 5822128775564748922877171)
                ·
                  refine ⟨8733193163347123384315757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5822128775564748922877171 8733193163347123384315757)
                  ·
                    refine ⟨3274947436255171269118409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8733193163347123384315757 3274947436255171269118409)
                    ·
                      refine ⟨2456210577191378451838807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3274947436255171269118409 2456210577191378451838807)
                      ·
                        rfl

theorem cell23_4783453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_4783453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783453 prefixEnd_4783453 := by exact prefixLift 4783453
  have htrace : WordTrace (prefixWord ++ tailWord_4783453) baseStart_4783453 baseEnd_4783453 := by
    simpa [prefixWord, tailWord_4783453, baseEnd_4783453] using wordTrace_append hprefix tailTrace_4783453
  have hstable : (prefixWord ++ tailWord_4783453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783453).length < 2 ^ (prefixWord ++ tailWord_4783453).sum := by decide
  have hdescent : baseEnd_4783453 < baseStart_4783453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783461 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 3, 2, 5]
def baseStart_4783461 : Nat := 118140960795 + 4783461 * 2 ^ 59
def prefixEnd_4783461 : Nat := 4983230072969 + 3 ^ 40 * 4783461 * 2
def baseEnd_4783461 : Nat := 2456214685036614420538769

theorem tailTrace_4783461 : CollatzResearch.WordTrace tailWord_4783461 prefixEnd_4783461 2456214685036614420538769 := by
  unfold tailWord_4783461
  simp only [CollatzResearch.WordTrace]
  refine ⟨174467155723345221943190237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116311437148896814628793491 174467155723345221943190237)
  ·
    refine ⟨65425183396254458228696339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174467155723345221943190237 65425183396254458228696339)
    ·
      refine ⟨98137775094381687343044509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65425183396254458228696339 98137775094381687343044509)
      ·
        refine ⟨36801665660393132753641691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98137775094381687343044509 36801665660393132753641691)
        ·
          refine ⟨55202498490589699130462537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36801665660393132753641691 55202498490589699130462537)
          ·
            refine ⟨41401873867942274347846903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55202498490589699130462537 41401873867942274347846903)
            ·
              refine ⟨62102810801913411521770355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41401873867942274347846903 62102810801913411521770355)
              ·
                refine ⟨93154216202870117282655533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62102810801913411521770355 93154216202870117282655533)
                ·
                  refine ⟨34932831076076293980995825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93154216202870117282655533 34932831076076293980995825)
                  ·
                    refine ⟨26199623307057220485746869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34932831076076293980995825 26199623307057220485746869)
                    ·
                      refine ⟨2456214685036614420538769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26199623307057220485746869 2456214685036614420538769)
                      ·
                        rfl

theorem cell23_4783461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_4783461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783461 prefixEnd_4783461 := by exact prefixLift 4783461
  have htrace : WordTrace (prefixWord ++ tailWord_4783461) baseStart_4783461 baseEnd_4783461 := by
    simpa [prefixWord, tailWord_4783461, baseEnd_4783461] using wordTrace_append hprefix tailTrace_4783461
  have hstable : (prefixWord ++ tailWord_4783461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783461).length < 2 ^ (prefixWord ++ tailWord_4783461).sum := by decide
  have hdescent : baseEnd_4783461 < baseStart_4783461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783468 : List Nat := [2, 2, 1, 1, 5, 1, 2, 2, 2, 5]
def baseStart_4783468 : Nat := 118140960795 + 4783468 * 2 ^ 59
def prefixEnd_4783468 : Nat := 4983230072969 + 3 ^ 40 * 4783468 * 2
def baseEnd_4783468 : Nat := 818739426467065297717079

theorem tailTrace_4783468 : CollatzResearch.WordTrace tailWord_4783468 prefixEnd_4783468 818739426467065297717079 := by
  unfold tailWord_4783468
  simp only [CollatzResearch.WordTrace]
  refine ⟨87233705517159931069347529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116311607356213241425796705 87233705517159931069347529)
  ·
    refine ⟨65425279137869948302010647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87233705517159931069347529 65425279137869948302010647)
    ·
      refine ⟨98137918706804922453015971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65425279137869948302010647 98137918706804922453015971)
      ·
        refine ⟨147206878060207383679523957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98137918706804922453015971 147206878060207383679523957)
        ·
          refine ⟨13800644818144442219955371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 147206878060207383679523957 13800644818144442219955371)
          ·
            refine ⟨20700967227216663329933057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13800644818144442219955371 20700967227216663329933057)
            ·
              refine ⟨15525725420412497497449793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20700967227216663329933057 15525725420412497497449793)
              ·
                refine ⟨11644294065309373123087345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15525725420412497497449793 11644294065309373123087345)
                ·
                  refine ⟨8733220548982029842315509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11644294065309373123087345 8733220548982029842315509)
                  ·
                    refine ⟨818739426467065297717079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8733220548982029842315509 818739426467065297717079)
                    ·
                      rfl

theorem cell23_4783468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 5].length) (baseStart_4783468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783468 prefixEnd_4783468 := by exact prefixLift 4783468
  have htrace : WordTrace (prefixWord ++ tailWord_4783468) baseStart_4783468 baseEnd_4783468 := by
    simpa [prefixWord, tailWord_4783468, baseEnd_4783468] using wordTrace_append hprefix tailTrace_4783468
  have hstable : (prefixWord ++ tailWord_4783468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783468).length < 2 ^ (prefixWord ++ tailWord_4783468).sum := by decide
  have hdescent : baseEnd_4783468 < baseStart_4783468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783502 : List Nat := [4, 1, 1, 4, 2, 2, 1, 1, 2, 5]
def baseStart_4783502 : Nat := 118140960795 + 4783502 * 2 ^ 59
def prefixEnd_4783502 : Nat := 4983230072969 + 3 ^ 40 * 4783502 * 2
def baseEnd_4783502 : Nat := 818745245914482920042027

theorem tailTrace_4783502 : CollatzResearch.WordTrace tailWord_4783502 prefixEnd_4783502 818745245914482920042027 := by
  unfold tailWord_4783502
  simp only [CollatzResearch.WordTrace]
  refine ⟨21808581389524585743179095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116312434077464457296955173 21808581389524585743179095)
  ·
    refine ⟨32712872084286878614768643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21808581389524585743179095 32712872084286878614768643)
    ·
      refine ⟨49069308126430317922152965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32712872084286878614768643 49069308126430317922152965)
      ·
        refine ⟨9200495273705684610403681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49069308126430317922152965 9200495273705684610403681)
        ·
          refine ⟨6900371455279263457802761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9200495273705684610403681 6900371455279263457802761)
          ·
            refine ⟨5175278591459447593352071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6900371455279263457802761 5175278591459447593352071)
            ·
              refine ⟨7762917887189171390028107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5175278591459447593352071 7762917887189171390028107)
              ·
                refine ⟨11644376830783757085042161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7762917887189171390028107 11644376830783757085042161)
                ·
                  refine ⟨8733282623087817813781621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11644376830783757085042161 8733282623087817813781621)
                  ·
                    refine ⟨818745245914482920042027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8733282623087817813781621 818745245914482920042027)
                    ·
                      rfl

theorem cell23_4783502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 2, 5].length) (baseStart_4783502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783502 prefixEnd_4783502 := by exact prefixLift 4783502
  have htrace : WordTrace (prefixWord ++ tailWord_4783502) baseStart_4783502 baseEnd_4783502 := by
    simpa [prefixWord, tailWord_4783502, baseEnd_4783502] using wordTrace_append hprefix tailTrace_4783502
  have hstable : (prefixWord ++ tailWord_4783502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783502).length < 2 ^ (prefixWord ++ tailWord_4783502).sum := by decide
  have hdescent : baseEnd_4783502 < baseStart_4783502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783511 : List Nat := [1, 1, 3, 3, 1, 1, 1, 4, 8]
def baseStart_4783511 : Nat := 118140960795 + 4783511 * 2 ^ 59
def prefixEnd_4783511 : Nat := 4983230072969 + 3 ^ 40 * 4783511 * 2
def baseEnd_4783511 : Nat := 272915595452148802768171

theorem tailTrace_4783511 : CollatzResearch.WordTrace tailWord_4783511 prefixEnd_4783511 272915595452148802768171 := by
  unfold tailWord_4783511
  simp only [CollatzResearch.WordTrace]
  refine ⟨174468979373164080482510387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116312652915442720321673591 174468979373164080482510387)
  ·
    refine ⟨261703469059746120723765581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174468979373164080482510387 261703469059746120723765581)
    ·
      refine ⟨98138800897404795271412093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 261703469059746120723765581 98138800897404795271412093)
      ·
        refine ⟨36802050336526798226779535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98138800897404795271412093 36802050336526798226779535)
        ·
          refine ⟨55203075504790197340169303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36802050336526798226779535 55203075504790197340169303)
          ·
            refine ⟨82804613257185296010253955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55203075504790197340169303 82804613257185296010253955)
            ·
              refine ⟨124206919885777944015380933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82804613257185296010253955 124206919885777944015380933)
              ·
                refine ⟨23288797478583364502883925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 124206919885777944015380933 23288797478583364502883925)
                ·
                  refine ⟨272915595452148802768171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23288797478583364502883925 272915595452148802768171)
                  ·
                    rfl

theorem cell23_4783511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 8].length) (baseStart_4783511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783511 prefixEnd_4783511 := by exact prefixLift 4783511
  have htrace : WordTrace (prefixWord ++ tailWord_4783511) baseStart_4783511 baseEnd_4783511 := by
    simpa [prefixWord, tailWord_4783511, baseEnd_4783511] using wordTrace_append hprefix tailTrace_4783511
  have hstable : (prefixWord ++ tailWord_4783511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783511).length < 2 ^ (prefixWord ++ tailWord_4783511).sum := by decide
  have hdescent : baseEnd_4783511 < baseStart_4783511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783551 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 7]
def baseStart_4783551 : Nat := 118140960795 + 4783551 * 2 ^ 59
def prefixEnd_4783551 : Nat := 4983230072969 + 3 ^ 40 * 4783551 * 2
def baseEnd_4783551 : Nat := 2456260898295519068413355

theorem tailTrace_4783551 : CollatzResearch.WordTrace tailWord_4783551 prefixEnd_4783551 2456260898295519068413355 := by
  unfold tailWord_4783551
  simp only [CollatzResearch.WordTrace]
  refine ⟨174470438293019167313966507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116313625528679444875977671 174470438293019167313966507)
  ·
    refine ⟨261705657439528750970949761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174470438293019167313966507 261705657439528750970949761)
    ·
      refine ⟨196279243079646563228212321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261705657439528750970949761 196279243079646563228212321)
      ·
        refine ⟨147209432309734922421159241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196279243079646563228212321 147209432309734922421159241)
        ·
          refine ⟨110407074232301191815869431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147209432309734922421159241 110407074232301191815869431)
          ·
            refine ⟨165610611348451787723804147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110407074232301191815869431 165610611348451787723804147)
            ·
              refine ⟨248415917022677681585706221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165610611348451787723804147 248415917022677681585706221)
              ·
                refine ⟨93155968883504130594639833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 248415917022677681585706221 93155968883504130594639833)
                ·
                  refine ⟨69866976662628097945979875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93155968883504130594639833 69866976662628097945979875)
                  ·
                    refine ⟨104800464993942146918969813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69866976662628097945979875 104800464993942146918969813)
                    ·
                      refine ⟨2456260898295519068413355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 104800464993942146918969813 2456260898295519068413355)
                      ·
                        rfl

theorem cell23_4783551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_4783551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783551 prefixEnd_4783551 := by exact prefixLift 4783551
  have htrace : WordTrace (prefixWord ++ tailWord_4783551) baseStart_4783551 baseEnd_4783551 := by
    simpa [prefixWord, tailWord_4783551, baseEnd_4783551] using wordTrace_append hprefix tailTrace_4783551
  have hstable : (prefixWord ++ tailWord_4783551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783551).length < 2 ^ (prefixWord ++ tailWord_4783551).sum := by decide
  have hdescent : baseEnd_4783551 < baseStart_4783551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783555 : List Nat := [1, 1, 1, 3, 1, 1, 6, 2, 3, 1, 3]
def baseStart_4783555 : Nat := 118140960795 + 4783555 * 2 ^ 59
def prefixEnd_4783555 : Nat := 4983230072969 + 3 ^ 40 * 4783555 * 2
def baseEnd_4783555 : Nat := 2456262952218137052763337

theorem tailTrace_4783555 : CollatzResearch.WordTrace tailWord_4783555 prefixEnd_4783555 2456262952218137052763337 := by
  unfold tailWord_4783555
  simp only [CollatzResearch.WordTrace]
  refine ⟨174470584185004675997112119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116313722790003117331408079 174470584185004675997112119)
  ·
    refine ⟨261705876277507013995668179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174470584185004675997112119 261705876277507013995668179)
    ·
      refine ⟨392558814416260520993502269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261705876277507013995668179 392558814416260520993502269)
      ·
        refine ⟨147209555406097695372563351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 392558814416260520993502269 147209555406097695372563351)
        ·
          refine ⟨220814333109146543058845027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147209555406097695372563351 220814333109146543058845027)
          ·
            refine ⟨331221499663719814588267541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220814333109146543058845027 331221499663719814588267541)
            ·
              refine ⟨15526007796736866308825041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 331221499663719814588267541 15526007796736866308825041)
              ·
                refine ⟨11644505847552649731618781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15526007796736866308825041 11644505847552649731618781)
                ·
                  refine ⟨4366689692832243649357043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11644505847552649731618781 4366689692832243649357043)
                  ·
                    refine ⟨6550034539248365474035565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4366689692832243649357043 6550034539248365474035565)
                    ·
                      refine ⟨2456262952218137052763337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6550034539248365474035565 2456262952218137052763337)
                      ·
                        rfl

theorem cell23_4783555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 3, 1, 3].length) (baseStart_4783555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783555 prefixEnd_4783555 := by exact prefixLift 4783555
  have htrace : WordTrace (prefixWord ++ tailWord_4783555) baseStart_4783555 baseEnd_4783555 := by
    simpa [prefixWord, tailWord_4783555, baseEnd_4783555] using wordTrace_append hprefix tailTrace_4783555
  have hstable : (prefixWord ++ tailWord_4783555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783555).length < 2 ^ (prefixWord ++ tailWord_4783555).sum := by decide
  have hdescent : baseEnd_4783555 < baseStart_4783555 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783589 : List Nat := [1, 3, 1, 5, 1, 3, 1, 1, 3, 1, 3]
def baseStart_4783589 : Nat := 118140960795 + 4783589 * 2 ^ 59
def prefixEnd_4783589 : Nat := 4983230072969 + 3 ^ 40 * 4783589 * 2
def baseEnd_4783589 : Nat := 2456280410560389919738181

theorem tailTrace_4783589 : CollatzResearch.WordTrace tailWord_4783589 prefixEnd_4783589 2456280410560389919738181 := by
  unfold tailWord_4783589
  simp only [CollatzResearch.WordTrace]
  refine ⟨174471824266881499803849821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116314549511254333202566547 174471824266881499803849821)
  ·
    refine ⟨65426934100080562426443683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174471824266881499803849821 65426934100080562426443683)
    ·
      refine ⟨98140401150120843639665525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65426934100080562426443683 98140401150120843639665525)
      ·
        refine ⟨9200662607823829091218643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 98140401150120843639665525 9200662607823829091218643)
        ·
          refine ⟨13800993911735743636827965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9200662607823829091218643 13800993911735743636827965)
          ·
            refine ⟨5175372716900903863810487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13800993911735743636827965 5175372716900903863810487)
            ·
              refine ⟨7763059075351355795715731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5175372716900903863810487 7763059075351355795715731)
              ·
                refine ⟨11644588613027033693573597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7763059075351355795715731 11644588613027033693573597)
                ·
                  refine ⟨4366720729885137635090099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11644588613027033693573597 4366720729885137635090099)
                  ·
                    refine ⟨6550081094827706452635149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4366720729885137635090099 6550081094827706452635149)
                    ·
                      refine ⟨2456280410560389919738181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6550081094827706452635149 2456280410560389919738181)
                      ·
                        rfl

theorem cell23_4783589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_4783589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783589 prefixEnd_4783589 := by exact prefixLift 4783589
  have htrace : WordTrace (prefixWord ++ tailWord_4783589) baseStart_4783589 baseEnd_4783589 := by
    simpa [prefixWord, tailWord_4783589, baseEnd_4783589] using wordTrace_append hprefix tailTrace_4783589
  have hstable : (prefixWord ++ tailWord_4783589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783589).length < 2 ^ (prefixWord ++ tailWord_4783589).sum := by decide
  have hdescent : baseEnd_4783589 < baseStart_4783589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783608 : List Nat := [2, 1, 2, 1, 1, 5, 2, 1, 1, 1, 6]
def baseStart_4783608 : Nat := 118140960795 + 4783608 * 2 ^ 59
def prefixEnd_4783608 : Nat := 4983230072969 + 3 ^ 40 * 4783608 * 2
def baseEnd_4783608 : Nat := 2456290166692825345400593

theorem tailTrace_4783608 : CollatzResearch.WordTrace tailWord_4783608 prefixEnd_4783608 2456290166692825345400593 := by
  unfold tailWord_4783608
  simp only [CollatzResearch.WordTrace]
  refine ⟨87236258626906333024395739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116315011502541777365860985 87236258626906333024395739)
  ·
    refine ⟨130854387940359499536593609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87236258626906333024395739 130854387940359499536593609)
    ·
      refine ⟨98140790955269624652445207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130854387940359499536593609 98140790955269624652445207)
      ·
        refine ⟨147211186432904436978667811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98140790955269624652445207 147211186432904436978667811)
        ·
          refine ⟨220816779649356655468001717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147211186432904436978667811 220816779649356655468001717)
          ·
            refine ⟨20701573092127186450125161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 220816779649356655468001717 20701573092127186450125161)
            ·
              refine ⟨15526179819095389837593871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20701573092127186450125161 15526179819095389837593871)
              ·
                refine ⟨23289269728643084756390807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15526179819095389837593871 23289269728643084756390807)
                ·
                  refine ⟨34933904592964627134586211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23289269728643084756390807 34933904592964627134586211)
                  ·
                    refine ⟨52400856889446940701879317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34933904592964627134586211 52400856889446940701879317)
                    ·
                      refine ⟨2456290166692825345400593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52400856889446940701879317 2456290166692825345400593)
                      ·
                        rfl

theorem cell23_4783608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 1, 1, 6].length) (baseStart_4783608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783608 prefixEnd_4783608 := by exact prefixLift 4783608
  have htrace : WordTrace (prefixWord ++ tailWord_4783608) baseStart_4783608 baseEnd_4783608 := by
    simpa [prefixWord, tailWord_4783608, baseEnd_4783608] using wordTrace_append hprefix tailTrace_4783608
  have hstable : (prefixWord ++ tailWord_4783608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783608).length < 2 ^ (prefixWord ++ tailWord_4783608).sum := by decide
  have hdescent : baseEnd_4783608 < baseStart_4783608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783612 : List Nat := [2, 2, 2, 1, 2, 1, 2, 4, 3, 2, 2]
def baseStart_4783612 : Nat := 118140960795 + 4783612 * 2 ^ 59
def prefixEnd_4783612 : Nat := 4983230072969 + 3 ^ 40 * 4783612 * 2
def baseEnd_4783612 : Nat := 2456292220615443329750575

theorem tailTrace_4783612 : CollatzResearch.WordTrace tailWord_4783612 prefixEnd_4783612 2456292220615443329750575 := by
  unfold tailWord_4783612
  simp only [CollatzResearch.WordTrace]
  refine ⟨87236331572899087365968545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116315108763865449821291393 87236331572899087365968545)
  ·
    refine ⟨65427248679674315524476409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87236331572899087365968545 65427248679674315524476409)
    ·
      refine ⟨49070436509755736643357307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65427248679674315524476409 49070436509755736643357307)
      ·
        refine ⟨73605654764633604965035961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49070436509755736643357307 73605654764633604965035961)
        ·
          refine ⟨55204241073475203723776971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73605654764633604965035961 55204241073475203723776971)
          ·
            refine ⟨82806361610212805585665457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55204241073475203723776971 82806361610212805585665457)
            ·
              refine ⟨62104771207659604189249093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82806361610212805585665457 62104771207659604189249093)
              ·
                refine ⟨11644644601436175785484205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62104771207659604189249093 11644644601436175785484205)
                ·
                  refine ⟨4366741725538565919556577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11644644601436175785484205 4366741725538565919556577)
                  ·
                    refine ⟨3275056294153924439667433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4366741725538565919556577 3275056294153924439667433)
                    ·
                      refine ⟨2456292220615443329750575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3275056294153924439667433 2456292220615443329750575)
                      ·
                        rfl

theorem cell23_4783612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 3, 2, 2].length) (baseStart_4783612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783612 prefixEnd_4783612 := by exact prefixLift 4783612
  have htrace : WordTrace (prefixWord ++ tailWord_4783612) baseStart_4783612 baseEnd_4783612 := by
    simpa [prefixWord, tailWord_4783612, baseEnd_4783612] using wordTrace_append hprefix tailTrace_4783612
  have hstable : (prefixWord ++ tailWord_4783612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783612).length < 2 ^ (prefixWord ++ tailWord_4783612).sum := by decide
  have hdescent : baseEnd_4783612 < baseStart_4783612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783615 : List Nat := [1, 1, 2, 2, 1, 2, 2, 6, 1, 2, 3]
def baseStart_4783615 : Nat := 118140960795 + 4783615 * 2 ^ 59
def prefixEnd_4783615 : Nat := 4983230072969 + 3 ^ 40 * 4783615 * 2
def baseEnd_4783615 : Nat := 2456293761057406818013061

theorem tailTrace_4783615 : CollatzResearch.WordTrace tailWord_4783615 prefixEnd_4783615 2456293761057406818013061 := by
  unfold tailWord_4783615
  simp only [CollatzResearch.WordTrace]
  refine ⟨174472772564787306244296299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116315181709858204162864199 174472772564787306244296299)
  ·
    refine ⟨261709158847180959366444449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174472772564787306244296299 261709158847180959366444449)
    ·
      refine ⟨196281869135385719524833337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261709158847180959366444449 196281869135385719524833337)
      ·
        refine ⟨147211401851539289643625003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196281869135385719524833337 147211401851539289643625003)
        ·
          refine ⟨220817102777308934465437505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147211401851539289643625003 220817102777308934465437505)
          ·
            refine ⟨165612827082981700849078129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220817102777308934465437505 165612827082981700849078129)
            ·
              refine ⟨124209620312236275636808597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165612827082981700849078129 124209620312236275636808597)
              ·
                refine ⟨5822325952136075420475403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 124209620312236275636808597 5822325952136075420475403)
                ·
                  refine ⟨8733488928204113130713105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5822325952136075420475403 8733488928204113130713105)
                  ·
                    refine ⟨6550116696153084848034829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8733488928204113130713105 6550116696153084848034829)
                    ·
                      refine ⟨2456293761057406818013061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6550116696153084848034829 2456293761057406818013061)
                      ·
                        rfl

theorem cell23_4783615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6, 1, 2, 3].length) (baseStart_4783615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783615 prefixEnd_4783615 := by exact prefixLift 4783615
  have htrace : WordTrace (prefixWord ++ tailWord_4783615) baseStart_4783615 baseEnd_4783615 := by
    simpa [prefixWord, tailWord_4783615, baseEnd_4783615] using wordTrace_append hprefix tailTrace_4783615
  have hstable : (prefixWord ++ tailWord_4783615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783615).length < 2 ^ (prefixWord ++ tailWord_4783615).sum := by decide
  have hdescent : baseEnd_4783615 < baseStart_4783615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783645 : List Nat := [1, 4, 2, 2, 1, 1, 1, 2, 3, 3, 3]
def baseStart_4783645 : Nat := 118140960795 + 4783645 * 2 ^ 59
def prefixEnd_4783645 : Nat := 4983230072969 + 3 ^ 40 * 4783645 * 2
def baseEnd_4783645 : Nat := 2456309165477041700637923

theorem tailTrace_4783645 : CollatzResearch.WordTrace tailWord_4783645 prefixEnd_4783645 2456309165477041700637923 := by
  unfold tailWord_4783645
  simp only [CollatzResearch.WordTrace]
  refine ⟨174473866754678621367888389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116315911169785747578592259 174473866754678621367888389)
  ·
    refine ⟨32713850016502241506479073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174473866754678621367888389 32713850016502241506479073)
    ·
      refine ⟨24535387512376681129859305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32713850016502241506479073 24535387512376681129859305)
      ·
        refine ⟨18401540634282510847394479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24535387512376681129859305 18401540634282510847394479)
        ·
          refine ⟨27602310951423766271091719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18401540634282510847394479 27602310951423766271091719)
          ·
            refine ⟨41403466427135649406637579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27602310951423766271091719 41403466427135649406637579)
            ·
              refine ⟨62105199640703474109956369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41403466427135649406637579 62105199640703474109956369)
              ·
                refine ⟨46578899730527605582467277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62105199640703474109956369 46578899730527605582467277)
                ·
                  refine ⟨17467087398947852093425229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46578899730527605582467277 17467087398947852093425229)
                  ·
                    refine ⟨6550157774605444535034461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17467087398947852093425229 6550157774605444535034461)
                    ·
                      refine ⟨2456309165477041700637923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6550157774605444535034461 2456309165477041700637923)
                      ·
                        rfl

theorem cell23_4783645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_4783645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783645 prefixEnd_4783645 := by exact prefixLift 4783645
  have htrace : WordTrace (prefixWord ++ tailWord_4783645) baseStart_4783645 baseEnd_4783645 := by
    simpa [prefixWord, tailWord_4783645, baseEnd_4783645] using wordTrace_append hprefix tailTrace_4783645
  have hstable : (prefixWord ++ tailWord_4783645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783645).length < 2 ^ (prefixWord ++ tailWord_4783645).sum := by decide
  have hdescent : baseEnd_4783645 < baseStart_4783645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783662 : List Nat := [4, 1, 3, 1, 2, 1, 1, 3, 1, 3, 3]
def baseStart_4783662 : Nat := 118140960795 + 4783662 * 2 ^ 59
def prefixEnd_4783662 : Nat := 4983230072969 + 3 ^ 40 * 4783662 * 2
def baseEnd_4783662 : Nat := 2456317894648168134125345

theorem tailTrace_4783662 : CollatzResearch.WordTrace tailWord_4783662 prefixEnd_4783662 2456317894648168134125345 := by
  unfold tailWord_4783662
  simp only [CollatzResearch.WordTrace]
  refine ⟨21809310849452129158907155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116316324530411355514171493 21809310849452129158907155)
  ·
    refine ⟨32713966274178193738360733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21809310849452129158907155 32713966274178193738360733)
    ·
      refine ⟨12267737352816822651885275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32713966274178193738360733 12267737352816822651885275)
      ·
        refine ⟨18401606029225233977827913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12267737352816822651885275 18401606029225233977827913)
        ·
          refine ⟨13801204521918925483370935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18401606029225233977827913 13801204521918925483370935)
          ·
            refine ⟨20701806782878388225056403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13801204521918925483370935 20701806782878388225056403)
            ·
              refine ⟨31052710174317582337584605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20701806782878388225056403 31052710174317582337584605)
              ·
                refine ⟨11644766315369093376594227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31052710174317582337584605 11644766315369093376594227)
                ·
                  refine ⟨17467149473053640064891341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11644766315369093376594227 17467149473053640064891341)
                  ·
                    refine ⟨6550181052395115024334253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17467149473053640064891341 6550181052395115024334253)
                    ·
                      refine ⟨2456317894648168134125345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6550181052395115024334253 2456317894648168134125345)
                      ·
                        rfl

theorem cell23_4783662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_4783662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783662 prefixEnd_4783662 := by exact prefixLift 4783662
  have htrace : WordTrace (prefixWord ++ tailWord_4783662) baseStart_4783662 baseEnd_4783662 := by
    simpa [prefixWord, tailWord_4783662, baseEnd_4783662] using wordTrace_append hprefix tailTrace_4783662
  have hstable : (prefixWord ++ tailWord_4783662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783662).length < 2 ^ (prefixWord ++ tailWord_4783662).sum := by decide
  have hdescent : baseEnd_4783662 < baseStart_4783662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783672 : List Nat := [2, 1, 2, 1, 4, 2, 2, 1, 3, 3, 2]
def baseStart_4783672 : Nat := 118140960795 + 4783672 * 2 ^ 59
def prefixEnd_4783672 : Nat := 4983230072969 + 3 ^ 40 * 4783672 * 2
def baseEnd_4783672 : Nat := 2456323029454713095000299

theorem tailTrace_4783672 : CollatzResearch.WordTrace tailWord_4783672 prefixEnd_4783672 2456323029454713095000299 := by
  unfold tailWord_4783672
  simp only [CollatzResearch.WordTrace]
  refine ⟨87237425762790402489560635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116316567683720536652747513 87237425762790402489560635)
  ·
    refine ⟨130856138644185603734340953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87237425762790402489560635 130856138644185603734340953)
    ·
      refine ⟨98142103983139202800755715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130856138644185603734340953 98142103983139202800755715)
      ·
        refine ⟨147213155974708804201133573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98142103983139202800755715 147213155974708804201133573)
        ·
          refine ⟨27602466745257900787712545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147213155974708804201133573 27602466745257900787712545)
          ·
            refine ⟨20701850058943425590784409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27602466745257900787712545 20701850058943425590784409)
            ·
              refine ⟨15526387544207569193088307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20701850058943425590784409 15526387544207569193088307)
              ·
                refine ⟨23289581316311353789632461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15526387544207569193088307 23289581316311353789632461)
                ·
                  refine ⟨8733592993616757671112173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23289581316311353789632461 8733592993616757671112173)
                  ·
                    refine ⟨3275097372606284126667065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8733592993616757671112173 3275097372606284126667065)
                    ·
                      refine ⟨2456323029454713095000299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3275097372606284126667065 2456323029454713095000299)
                      ·
                        rfl

theorem cell23_4783672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 3, 3, 2].length) (baseStart_4783672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783672 prefixEnd_4783672 := by exact prefixLift 4783672
  have htrace : WordTrace (prefixWord ++ tailWord_4783672) baseStart_4783672 baseEnd_4783672 := by
    simpa [prefixWord, tailWord_4783672, baseEnd_4783672] using wordTrace_append hprefix tailTrace_4783672
  have hstable : (prefixWord ++ tailWord_4783672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783672).length < 2 ^ (prefixWord ++ tailWord_4783672).sum := by decide
  have hdescent : baseEnd_4783672 < baseStart_4783672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783715 : List Nat := [1, 1, 1, 5, 1, 3, 2, 1, 2, 2, 4]
def baseStart_4783715 : Nat := 118140960795 + 4783715 * 2 ^ 59
def prefixEnd_4783715 : Nat := 4983230072969 + 3 ^ 40 * 4783715 * 2
def baseEnd_4783715 : Nat := 2456345109122856426762601

theorem tailTrace_4783715 : CollatzResearch.WordTrace tailWord_4783715 prefixEnd_4783715 2456345109122856426762601 := by
  unfold tailWord_4783715
  simp only [CollatzResearch.WordTrace]
  refine ⟨174476419864425023322936599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116317613242950015548624399 174476419864425023322936599)
  ·
    refine ⟨261714629796637534984404899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174476419864425023322936599 261714629796637534984404899)
    ·
      refine ⟨392571944694956302476607349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261714629796637534984404899 392571944694956302476607349)
      ·
        refine ⟨36803619815152153357181939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 392571944694956302476607349 36803619815152153357181939)
        ·
          refine ⟨55205429722728230035772909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36803619815152153357181939 55205429722728230035772909)
          ·
            refine ⟨20702036146023086263414841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55205429722728230035772909 20702036146023086263414841)
            ·
              refine ⟨15526527109517314697561131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20702036146023086263414841 15526527109517314697561131)
              ·
                refine ⟨23289790664275972046341697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15526527109517314697561131 23289790664275972046341697)
                ·
                  refine ⟨17467342998206979034756273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23289790664275972046341697 17467342998206979034756273)
                  ·
                    refine ⟨13100507248655234276067205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17467342998206979034756273 13100507248655234276067205)
                    ·
                      refine ⟨2456345109122856426762601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13100507248655234276067205 2456345109122856426762601)
                      ·
                        rfl

theorem cell23_4783715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_4783715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783715 prefixEnd_4783715 := by exact prefixLift 4783715
  have htrace : WordTrace (prefixWord ++ tailWord_4783715) baseStart_4783715 baseEnd_4783715 := by
    simpa [prefixWord, tailWord_4783715, baseEnd_4783715] using wordTrace_append hprefix tailTrace_4783715
  have hstable : (prefixWord ++ tailWord_4783715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783715).length < 2 ^ (prefixWord ++ tailWord_4783715).sum := by decide
  have hdescent : baseEnd_4783715 < baseStart_4783715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783719 : List Nat := [1, 1, 5, 1, 1, 1, 2, 5, 2, 2, 2]
def baseStart_4783719 : Nat := 118140960795 + 4783719 * 2 ^ 59
def prefixEnd_4783719 : Nat := 4983230072969 + 3 ^ 40 * 4783719 * 2
def baseEnd_4783719 : Nat := 2456347163045474411112583

theorem tailTrace_4783719 : CollatzResearch.WordTrace tailWord_4783719 prefixEnd_4783719 2456347163045474411112583 := by
  unfold tailWord_4783719
  simp only [CollatzResearch.WordTrace]
  refine ⟨174476565756410532006082211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116317710504273688004054807 174476565756410532006082211)
  ·
    refine ⟨261714848634615798009123317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174476565756410532006082211 261714848634615798009123317)
    ·
      refine ⟨24535767059495231063355311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 261714848634615798009123317 24535767059495231063355311)
      ·
        refine ⟨36803650589242846595032967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24535767059495231063355311 36803650589242846595032967)
        ·
          refine ⟨55205475883864269892549451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36803650589242846595032967 55205475883864269892549451)
          ·
            refine ⟨82808213825796404838824177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55205475883864269892549451 82808213825796404838824177)
            ·
              refine ⟨62106160369347303629118133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82808213825796404838824177 62106160369347303629118133)
              ·
                refine ⟨5822452534626309715229825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62106160369347303629118133 5822452534626309715229825)
                ·
                  refine ⟨4366839400969732286422369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5822452534626309715229825 4366839400969732286422369)
                  ·
                    refine ⟨3275129550727299214816777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4366839400969732286422369 3275129550727299214816777)
                    ·
                      refine ⟨2456347163045474411112583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3275129550727299214816777 2456347163045474411112583)
                      ·
                        rfl

theorem cell23_4783719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5, 2, 2, 2].length) (baseStart_4783719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783719 prefixEnd_4783719 := by exact prefixLift 4783719
  have htrace : WordTrace (prefixWord ++ tailWord_4783719) baseStart_4783719 baseEnd_4783719 := by
    simpa [prefixWord, tailWord_4783719, baseEnd_4783719] using wordTrace_append hprefix tailTrace_4783719
  have hstable : (prefixWord ++ tailWord_4783719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783719).length < 2 ^ (prefixWord ++ tailWord_4783719).sum := by decide
  have hdescent : baseEnd_4783719 < baseStart_4783719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783755 : List Nat := [1, 1, 1, 1, 4, 1, 5, 2, 2, 5]
def baseStart_4783755 : Nat := 118140960795 + 4783755 * 2 ^ 59
def prefixEnd_4783755 : Nat := 4983230072969 + 3 ^ 40 * 4783755 * 2
def baseEnd_4783755 : Nat := 818788549449678756754139

theorem tailTrace_4783755 : CollatzResearch.WordTrace tailWord_4783755 prefixEnd_4783755 818788549449678756754139 := by
  unfold tailWord_4783755
  simp only [CollatzResearch.WordTrace]
  refine ⟨174477878784280110154392719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116318585856186740102928479 174477878784280110154392719)
  ·
    refine ⟨261716818176420165231589079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174477878784280110154392719 261716818176420165231589079)
    ·
      refine ⟨392575227264630247847383619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261716818176420165231589079 392575227264630247847383619)
      ·
        refine ⟨588862840896945371771075429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 392575227264630247847383619 588862840896945371771075429)
        ·
          refine ⟨110411782668177257207076643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 588862840896945371771075429 110411782668177257207076643)
          ·
            refine ⟨165617674002265885810614965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110411782668177257207076643 165617674002265885810614965)
            ·
              refine ⟨15526656937712426794745153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 165617674002265885810614965 15526656937712426794745153)
              ·
                refine ⟨11644992703284320096058865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15526656937712426794745153 11644992703284320096058865)
                ·
                  refine ⟨8733744527463240072044149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11644992703284320096058865 8733744527463240072044149)
                  ·
                    refine ⟨818788549449678756754139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8733744527463240072044149 818788549449678756754139)
                    ·
                      rfl

theorem cell23_4783755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2, 5].length) (baseStart_4783755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783755 prefixEnd_4783755 := by exact prefixLift 4783755
  have htrace : WordTrace (prefixWord ++ tailWord_4783755) baseStart_4783755 baseEnd_4783755 := by
    simpa [prefixWord, tailWord_4783755, baseEnd_4783755] using wordTrace_append hprefix tailTrace_4783755
  have hstable : (prefixWord ++ tailWord_4783755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783755).length < 2 ^ (prefixWord ++ tailWord_4783755).sum := by decide
  have hdescent : baseEnd_4783755 < baseStart_4783755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783805 : List Nat := [1, 4, 1, 2, 1, 2, 2, 1, 2, 1, 6]
def baseStart_4783805 : Nat := 118140960795 + 4783805 * 2 ^ 59
def prefixEnd_4783805 : Nat := 4983230072969 + 3 ^ 40 * 4783805 * 2
def baseEnd_4783805 : Nat := 2456391322381761074637187

theorem tailTrace_4783805 : CollatzResearch.WordTrace tailWord_4783805 prefixEnd_4783805 2456391322381761074637187 := by
  unfold tailWord_4783805
  simp only [CollatzResearch.WordTrace]
  refine ⟨174479702434098968693712869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116319801622732645795808579 174479702434098968693712869)
  ·
    refine ⟨32714944206393556630071163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174479702434098968693712869 32714944206393556630071163)
    ·
      refine ⟨49072416309590334945106745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32714944206393556630071163 49072416309590334945106745)
      ·
        refine ⟨36804312232192751208830059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49072416309590334945106745 36804312232192751208830059)
        ·
          refine ⟨55206468348289126813245089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36804312232192751208830059 55206468348289126813245089)
          ·
            refine ⟨41404851261216845109933817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55206468348289126813245089 41404851261216845109933817)
            ·
              refine ⟨31053638445912633832450363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41404851261216845109933817 31053638445912633832450363)
              ·
                refine ⟨46580457668868950748675545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31053638445912633832450363 46580457668868950748675545)
                ·
                  refine ⟨34935343251651713061506659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46580457668868950748675545 34935343251651713061506659)
                  ·
                    refine ⟨52403014877477569592259989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34935343251651713061506659 52403014877477569592259989)
                    ·
                      refine ⟨2456391322381761074637187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52403014877477569592259989 2456391322381761074637187)
                      ·
                        rfl

theorem cell23_4783805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_4783805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783805 prefixEnd_4783805 := by exact prefixLift 4783805
  have htrace : WordTrace (prefixWord ++ tailWord_4783805) baseStart_4783805 baseEnd_4783805 := by
    simpa [prefixWord, tailWord_4783805, baseEnd_4783805] using wordTrace_append hprefix tailTrace_4783805
  have hstable : (prefixWord ++ tailWord_4783805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783805).length < 2 ^ (prefixWord ++ tailWord_4783805).sum := by decide
  have hdescent : baseEnd_4783805 < baseStart_4783805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783836 : List Nat := [2, 2, 5, 1, 2, 1, 1, 2, 3, 4]
def baseStart_4783836 : Nat := 118140960795 + 4783836 * 2 ^ 59
def prefixEnd_4783836 : Nat := 4983230072969 + 3 ^ 40 * 4783836 * 2
def baseEnd_4783836 : Nat := 818802413427350151116515

theorem tailTrace_4783836 : CollatzResearch.WordTrace tailWord_4783836 prefixEnd_4783836 818802413427350151116515 := by
  unfold tailWord_4783836
  simp only [CollatzResearch.WordTrace]
  refine ⟨87240416548493330494045681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116320555397991107325394241 87240416548493330494045681)
  ·
    refine ⟨65430312411369997870534261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87240416548493330494045681 65430312411369997870534261)
    ·
      refine ⟨6134091788565937300362587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65430312411369997870534261 6134091788565937300362587)
      ·
        refine ⟨9201137682848905950543881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6134091788565937300362587 9201137682848905950543881)
        ·
          refine ⟨6900853262136679462907911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9201137682848905950543881 6900853262136679462907911)
          ·
            refine ⟨10351279893205019194361867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6900853262136679462907911 10351279893205019194361867)
            ·
              refine ⟨15526919839807528791542801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10351279893205019194361867 15526919839807528791542801)
              ·
                refine ⟨11645189879855646593657101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15526919839807528791542801 11645189879855646593657101)
                ·
                  refine ⟨4366946204945867472621413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11645189879855646593657101 4366946204945867472621413)
                  ·
                    refine ⟨818802413427350151116515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4366946204945867472621413 818802413427350151116515)
                    ·
                      rfl

theorem cell23_4783836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_4783836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783836 prefixEnd_4783836 := by exact prefixLift 4783836
  have htrace : WordTrace (prefixWord ++ tailWord_4783836) baseStart_4783836 baseEnd_4783836 := by
    simpa [prefixWord, tailWord_4783836, baseEnd_4783836] using wordTrace_append hprefix tailTrace_4783836
  have hstable : (prefixWord ++ tailWord_4783836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783836).length < 2 ^ (prefixWord ++ tailWord_4783836).sum := by decide
  have hdescent : baseEnd_4783836 < baseStart_4783836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783875 : List Nat := [1, 1, 1, 3, 2, 2, 2, 2, 3, 6]
def baseStart_4783875 : Nat := 118140960795 + 4783875 * 2 ^ 59
def prefixEnd_4783875 : Nat := 4983230072969 + 3 ^ 40 * 4783875 * 2
def baseEnd_4783875 : Nat := 818809088675858600253955

theorem tailTrace_4783875 : CollatzResearch.WordTrace tailWord_4783875 prefixEnd_4783875 818809088675858600253955 := by
  unfold tailWord_4783875
  simp only [CollatzResearch.WordTrace]
  refine ⟨174482255543845370648761079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116321503695896913765840719 174482255543845370648761079)
  ·
    refine ⟨261723383315768055973141619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174482255543845370648761079 261723383315768055973141619)
    ·
      refine ⟨392585074973652083959712429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261723383315768055973141619 392585074973652083959712429)
      ·
        refine ⟨147219403115119531484892161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 392585074973652083959712429 147219403115119531484892161)
        ·
          refine ⟨110414552336339648613669121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147219403115119531484892161 110414552336339648613669121)
          ·
            refine ⟨82810914252254736460251841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110414552336339648613669121 82810914252254736460251841)
            ·
              refine ⟨62108185689191052345188881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82810914252254736460251841 62108185689191052345188881)
              ·
                refine ⟨46581139266893289258891661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62108185689191052345188881 46581139266893289258891661)
                ·
                  refine ⟨17467927225084983472084373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46581139266893289258891661 17467927225084983472084373)
                  ·
                    refine ⟨818809088675858600253955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17467927225084983472084373 818809088675858600253955)
                    ·
                      rfl

theorem cell23_4783875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 6].length) (baseStart_4783875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783875 prefixEnd_4783875 := by exact prefixLift 4783875
  have htrace : WordTrace (prefixWord ++ tailWord_4783875) baseStart_4783875 baseEnd_4783875 := by
    simpa [prefixWord, tailWord_4783875, baseEnd_4783875] using wordTrace_append hprefix tailTrace_4783875
  have hstable : (prefixWord ++ tailWord_4783875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783875).length < 2 ^ (prefixWord ++ tailWord_4783875).sum := by decide
  have hdescent : baseEnd_4783875 < baseStart_4783875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783876 : List Nat := [2, 3, 2, 2, 1, 3, 2, 1, 3, 1, 3]
def baseStart_4783876 : Nat := 118140960795 + 4783876 * 2 ^ 59
def prefixEnd_4783876 : Nat := 4983230072969 + 3 ^ 40 * 4783876 * 2
def baseEnd_4783876 : Nat := 2456427779508230296849361

theorem tailTrace_4783876 : CollatzResearch.WordTrace tailWord_4783876 prefixEnd_4783876 2456427779508230296849361 := by
  unfold tailWord_4783876
  simp only [CollatzResearch.WordTrace]
  refine ⟨87241146008420873909773741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116321528011227831879698321 87241146008420873909773741)
  ·
    refine ⟨32715429753157827716165153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87241146008420873909773741 32715429753157827716165153)
    ·
      refine ⟨24536572314868370787123865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32715429753157827716165153 24536572314868370787123865)
      ·
        refine ⟨18402429236151278090342899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24536572314868370787123865 18402429236151278090342899)
        ·
          refine ⟨27603643854226917135514349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18402429236151278090342899 27603643854226917135514349)
          ·
            refine ⟨10351366445335093925817881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27603643854226917135514349 10351366445335093925817881)
            ·
              refine ⟨7763524834001320444363411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10351366445335093925817881 7763524834001320444363411)
              ·
                refine ⟨11645287251001980666545117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7763524834001320444363411 11645287251001980666545117)
                ·
                  refine ⟨4366982719125742749954419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11645287251001980666545117 4366982719125742749954419)
                  ·
                    refine ⟨6550474078688614124931629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4366982719125742749954419 6550474078688614124931629)
                    ·
                      refine ⟨2456427779508230296849361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6550474078688614124931629 2456427779508230296849361)
                      ·
                        rfl

theorem cell23_4783876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_4783876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783876 prefixEnd_4783876 := by exact prefixLift 4783876
  have htrace : WordTrace (prefixWord ++ tailWord_4783876) baseStart_4783876 baseEnd_4783876 := by
    simpa [prefixWord, tailWord_4783876, baseEnd_4783876] using wordTrace_append hprefix tailTrace_4783876
  have hstable : (prefixWord ++ tailWord_4783876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783876).length < 2 ^ (prefixWord ++ tailWord_4783876).sum := by decide
  have hdescent : baseEnd_4783876 < baseStart_4783876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783922 : List Nat := [3, 2, 1, 1, 3, 4, 9]
def baseStart_4783922 : Nat := 118140960795 + 4783922 * 2 ^ 59
def prefixEnd_4783922 : Nat := 4983230072969 + 3 ^ 40 * 4783922 * 2
def baseEnd_4783922 : Nat := 30326560489115273047829

theorem tailTrace_4783922 : CollatzResearch.WordTrace tailWord_4783922 prefixEnd_4783922 30326560489115273047829 := by
  unfold tailWord_4783922
  simp only [CollatzResearch.WordTrace]
  refine ⟨43620992443668774418930505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116322646516450065117148013 43620992443668774418930505)
  ·
    refine ⟨32715744332751580814197879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43620992443668774418930505 32715744332751580814197879)
    ·
      refine ⟨49073616499127371221296819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32715744332751580814197879 49073616499127371221296819)
      ·
        refine ⟨73610424748691056831945229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49073616499127371221296819 73610424748691056831945229)
        ·
          refine ⟨27603909280759146311979461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73610424748691056831945229 27603909280759146311979461)
          ·
            refine ⟨5175732990142339933496149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27603909280759146311979461 5175732990142339933496149)
            ·
              refine ⟨30326560489115273047829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5175732990142339933496149 30326560489115273047829)
              ·
                rfl

theorem cell23_4783922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 9].length) (baseStart_4783922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783922 prefixEnd_4783922 := by exact prefixLift 4783922
  have htrace : WordTrace (prefixWord ++ tailWord_4783922) baseStart_4783922 baseEnd_4783922 := by
    simpa [prefixWord, tailWord_4783922, baseEnd_4783922] using wordTrace_append hprefix tailTrace_4783922
  have hstable : (prefixWord ++ tailWord_4783922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783922).length < 2 ^ (prefixWord ++ tailWord_4783922).sum := by decide
  have hdescent : baseEnd_4783922 < baseStart_4783922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783926 : List Nat := [5, 1, 2, 2, 1, 1, 2, 1, 4, 4]
def baseStart_4783926 : Nat := 118140960795 + 4783926 * 2 ^ 59
def prefixEnd_4783926 : Nat := 4983230072969 + 3 ^ 40 * 4783926 * 2
def baseEnd_4783926 : Nat := 818817817846985033741377

theorem tailTrace_4783926 : CollatzResearch.WordTrace tailWord_4783926 prefixEnd_4783926 818817817846985033741377 := by
  unfold tailWord_4783926
  simp only [CollatzResearch.WordTrace]
  refine ⟨10905257229166287897429227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116322743777773737572578421 10905257229166287897429227)
  ·
    refine ⟨16357885843749431846143841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10905257229166287897429227 16357885843749431846143841)
    ·
      refine ⟨12268414382812073884607881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16357885843749431846143841 12268414382812073884607881)
      ·
        refine ⟨9201310787109055413455911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12268414382812073884607881 9201310787109055413455911)
        ·
          refine ⟨13801966180663583120183867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9201310787109055413455911 13801966180663583120183867)
          ·
            refine ⟨20702949270995374680275801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13801966180663583120183867 20702949270995374680275801)
            ·
              refine ⟨15527211953246531010206851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20702949270995374680275801 15527211953246531010206851)
              ·
                refine ⟨23290817929869796515310277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15527211953246531010206851 23290817929869796515310277)
                ·
                  refine ⟨4367028361850586846620677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23290817929869796515310277 4367028361850586846620677)
                  ·
                    refine ⟨818817817846985033741377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4367028361850586846620677 818817817846985033741377)
                    ·
                      rfl

theorem cell23_4783926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_4783926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783926 prefixEnd_4783926 := by exact prefixLift 4783926
  have htrace : WordTrace (prefixWord ++ tailWord_4783926) baseStart_4783926 baseEnd_4783926 := by
    simpa [prefixWord, tailWord_4783926, baseEnd_4783926] using wordTrace_append hprefix tailTrace_4783926
  have hstable : (prefixWord ++ tailWord_4783926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783926).length < 2 ^ (prefixWord ++ tailWord_4783926).sum := by decide
  have hdescent : baseEnd_4783926 < baseStart_4783926 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783933 : List Nat := [1, 4, 1, 4, 1, 1, 3, 1, 3, 2, 2]
def baseStart_4783933 : Nat := 118140960795 + 4783933 * 2 ^ 59
def prefixEnd_4783933 : Nat := 4983230072969 + 3 ^ 40 * 4783933 * 2
def baseEnd_4783933 : Nat := 2456457047905536573836599

theorem tailTrace_4783933 : CollatzResearch.WordTrace tailWord_4783933 prefixEnd_4783933 2456457047905536573836599 := by
  unfold tailWord_4783933
  simp only [CollatzResearch.WordTrace]
  refine ⟨174484370977635246554372453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116322913985090164369581635 174484370977635246554372453)
  ·
    refine ⟨32715819558306608728944835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174484370977635246554372453 32715819558306608728944835)
    ·
      refine ⟨49073729337459913093417253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32715819558306608728944835 49073729337459913093417253)
      ·
        refine ⟨9201324250773733705015735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49073729337459913093417253 9201324250773733705015735)
        ·
          refine ⟨13801986376160600557523603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9201324250773733705015735 13801986376160600557523603)
          ·
            refine ⟨20702979564240900836285405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13801986376160600557523603 20702979564240900836285405)
            ·
              refine ⟨7763617336590337813607027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20702979564240900836285405 7763617336590337813607027)
              ·
                refine ⟨11645426004885506720410541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7763617336590337813607027 11645426004885506720410541)
                ·
                  refine ⟨4367034751832065020153953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11645426004885506720410541 4367034751832065020153953)
                  ·
                    refine ⟨3275276063874048765115465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4367034751832065020153953 3275276063874048765115465)
                    ·
                      refine ⟨2456457047905536573836599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3275276063874048765115465 2456457047905536573836599)
                      ·
                        rfl

theorem cell23_4783933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_4783933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783933 prefixEnd_4783933 := by exact prefixLift 4783933
  have htrace : WordTrace (prefixWord ++ tailWord_4783933) baseStart_4783933 baseEnd_4783933 := by
    simpa [prefixWord, tailWord_4783933, baseEnd_4783933] using wordTrace_append hprefix tailTrace_4783933
  have hstable : (prefixWord ++ tailWord_4783933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783933).length < 2 ^ (prefixWord ++ tailWord_4783933).sum := by decide
  have hdescent : baseEnd_4783933 < baseStart_4783933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4783955 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 10]
def baseStart_4783955 : Nat := 118140960795 + 4783955 * 2 ^ 59
def prefixEnd_4783955 : Nat := 4983230072969 + 3 ^ 40 * 4783955 * 2
def baseEnd_4783955 : Nat := 2456468344479935487761497

theorem tailTrace_4783955 : CollatzResearch.WordTrace tailWord_4783955 prefixEnd_4783955 2456468344479935487761497 := by
  unfold tailWord_4783955
  simp only [CollatzResearch.WordTrace]
  refine ⟨174485173383555544311673319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116323448922370362874448879 174485173383555544311673319)
  ·
    refine ⟨261727760075333316467509979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174485173383555544311673319 261727760075333316467509979)
    ·
      refine ⟨392591640112999974701264969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261727760075333316467509979 392591640112999974701264969)
      ·
        refine ⟨294443730084749981025948727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 392591640112999974701264969 294443730084749981025948727)
        ·
          refine ⟨441665595127124971538923091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294443730084749981025948727 441665595127124971538923091)
          ·
            refine ⟨662498392690687457308384637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 441665595127124971538923091 662498392690687457308384637)
            ·
              refine ⟨248436897259007796490644239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 662498392690687457308384637 248436897259007796490644239)
              ·
                refine ⟨372655345888511694735966359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248436897259007796490644239 372655345888511694735966359)
                ·
                  refine ⟨558983018832767542103949539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 372655345888511694735966359 558983018832767542103949539)
                  ·
                    refine ⟨838474528249151313155924309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 558983018832767542103949539 838474528249151313155924309)
                    ·
                      refine ⟨2456468344479935487761497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 838474528249151313155924309 2456468344479935487761497)
                      ·
                        rfl

theorem cell23_4783955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 10].length) (baseStart_4783955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4783955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4783955 prefixEnd_4783955 := by exact prefixLift 4783955
  have htrace : WordTrace (prefixWord ++ tailWord_4783955) baseStart_4783955 baseEnd_4783955 := by
    simpa [prefixWord, tailWord_4783955, baseEnd_4783955] using wordTrace_append hprefix tailTrace_4783955
  have hstable : (prefixWord ++ tailWord_4783955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4783955).length < 2 ^ (prefixWord ++ tailWord_4783955).sum := by decide
  have hdescent : baseEnd_4783955 < baseStart_4783955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4783955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784079 : List Nat := [1, 1, 2, 1, 1, 5, 2, 3, 2, 1, 4]
def baseStart_4784079 : Nat := 118140960795 + 4784079 * 2 ^ 59
def prefixEnd_4784079 : Nat := 4983230072969 + 3 ^ 40 * 4784079 * 2
def baseEnd_4784079 : Nat := 2456532016081093002610927

theorem tailTrace_4784079 : CollatzResearch.WordTrace tailWord_4784079 prefixEnd_4784079 2456532016081093002610927 := by
  unfold tailWord_4784079
  simp only [CollatzResearch.WordTrace]
  refine ⟨174489696035106313489187291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116326464023404208992791527 174489696035106313489187291)
  ·
    refine ⟨261734544052659470233780937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174489696035106313489187291 261734544052659470233780937)
    ·
      refine ⟨196300908039494602675335703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261734544052659470233780937 196300908039494602675335703)
      ·
        refine ⟨294451362059241904013003555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196300908039494602675335703 294451362059241904013003555)
        ·
          refine ⟨441677043088862856019505333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294451362059241904013003555 441677043088862856019505333)
          ·
            refine ⟨41407222789580892751828625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 441677043088862856019505333 41407222789580892751828625)
            ·
              refine ⟨31055417092185669563871469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41407222789580892751828625 31055417092185669563871469)
              ·
                refine ⟨11645781409569626086451801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31055417092185669563871469 11645781409569626086451801)
                ·
                  refine ⟨8734336057177219564838851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11645781409569626086451801 8734336057177219564838851)
                  ·
                    refine ⟨13101504085765829347258277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8734336057177219564838851 13101504085765829347258277)
                    ·
                      refine ⟨2456532016081093002610927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13101504085765829347258277 2456532016081093002610927)
                      ·
                        rfl

theorem cell23_4784079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2, 1, 4].length) (baseStart_4784079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784079 prefixEnd_4784079 := by exact prefixLift 4784079
  have htrace : WordTrace (prefixWord ++ tailWord_4784079) baseStart_4784079 baseEnd_4784079 := by
    simpa [prefixWord, tailWord_4784079, baseEnd_4784079] using wordTrace_append hprefix tailTrace_4784079
  have hstable : (prefixWord ++ tailWord_4784079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784079).length < 2 ^ (prefixWord ++ tailWord_4784079).sum := by decide
  have hdescent : baseEnd_4784079 < baseStart_4784079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784157 : List Nat := [1, 4, 2, 2, 2, 3, 2, 2, 1, 4]
def baseStart_4784157 : Nat := 118140960795 + 4784157 * 2 ^ 59
def prefixEnd_4784157 : Nat := 4983230072969 + 3 ^ 40 * 4784157 * 2
def baseEnd_4784157 : Nat := 818857355857381232478523

theorem tailTrace_4784157 : CollatzResearch.WordTrace tailWord_4784157 prefixEnd_4784157 818857355857381232478523 := by
  unfold tailWord_4784157
  simp only [CollatzResearch.WordTrace]
  refine ⟨174492540928823732810526725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116328360619215821873684483 174492540928823732810526725)
  ·
    refine ⟨32717351424154449901973761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174492540928823732810526725 32717351424154449901973761)
    ·
      refine ⟨24538013568115837426480321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32717351424154449901973761 24538013568115837426480321)
      ·
        refine ⟨18403510176086878069860241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24538013568115837426480321 18403510176086878069860241)
        ·
          refine ⟨13802632632065158552395181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18403510176086878069860241 13802632632065158552395181)
          ·
            refine ⟨5175987237024434457148193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13802632632065158552395181 5175987237024434457148193)
            ·
              refine ⟨3881990427768325842861145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5175987237024434457148193 3881990427768325842861145)
              ·
                refine ⟨2911492820826244382145859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3881990427768325842861145 2911492820826244382145859)
                ·
                  refine ⟨4367239231239366573218789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2911492820826244382145859 4367239231239366573218789)
                  ·
                    refine ⟨818857355857381232478523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4367239231239366573218789 818857355857381232478523)
                    ·
                      rfl

theorem cell23_4784157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_4784157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784157 prefixEnd_4784157 := by exact prefixLift 4784157
  have htrace : WordTrace (prefixWord ++ tailWord_4784157) baseStart_4784157 baseEnd_4784157 := by
    simpa [prefixWord, tailWord_4784157, baseEnd_4784157] using wordTrace_append hprefix tailTrace_4784157
  have hstable : (prefixWord ++ tailWord_4784157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784157).length < 2 ^ (prefixWord ++ tailWord_4784157).sum := by decide
  have hdescent : baseEnd_4784157 < baseStart_4784157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784179 : List Nat := [1, 1, 1, 2, 4, 1, 3, 3, 1, 6]
def baseStart_4784179 : Nat := 118140960795 + 4784179 * 2 ^ 59
def prefixEnd_4784179 : Nat := 4983230072969 + 3 ^ 40 * 4784179 * 2
def baseEnd_4784179 : Nat := 818861121382180870453489

theorem tailTrace_4784179 : CollatzResearch.WordTrace tailWord_4784179 prefixEnd_4784179 818861121382180870453489 := by
  unfold tailWord_4784179
  simp only [CollatzResearch.WordTrace]
  refine ⟨174493343334744030567827591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116328895556496020378551727 174493343334744030567827591)
  ·
    refine ⟨261740015002116045851741387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174493343334744030567827591 261740015002116045851741387)
    ·
      refine ⟨392610022503174068777612081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261740015002116045851741387 392610022503174068777612081)
      ·
        refine ⟨294457516877380551583209061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 392610022503174068777612081 294457516877380551583209061)
        ·
          refine ⟨55210784414508853421851699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 294457516877380551583209061 55210784414508853421851699)
          ·
            refine ⟨82816176621763280132777549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55210784414508853421851699 82816176621763280132777549)
            ·
              refine ⟨31056066233161230049791581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82816176621763280132777549 31056066233161230049791581)
              ·
                refine ⟨11646024837435461268671843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31056066233161230049791581 11646024837435461268671843)
                ·
                  refine ⟨17469037256153191903007765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11646024837435461268671843 17469037256153191903007765)
                  ·
                    refine ⟨818861121382180870453489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17469037256153191903007765 818861121382180870453489)
                    ·
                      rfl

theorem cell23_4784179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 6].length) (baseStart_4784179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784179 prefixEnd_4784179 := by exact prefixLift 4784179
  have htrace : WordTrace (prefixWord ++ tailWord_4784179) baseStart_4784179 baseEnd_4784179 := by
    simpa [prefixWord, tailWord_4784179, baseEnd_4784179] using wordTrace_append hprefix tailTrace_4784179
  have hstable : (prefixWord ++ tailWord_4784179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784179).length < 2 ^ (prefixWord ++ tailWord_4784179).sum := by decide
  have hdescent : baseEnd_4784179 < baseStart_4784179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784186 : List Nat := [3, 1, 1, 1, 3, 1, 1, 6, 1, 1, 4]
def baseStart_4784186 : Nat := 118140960795 + 4784186 * 2 ^ 59
def prefixEnd_4784186 : Nat := 4983230072969 + 3 ^ 40 * 4784186 * 2
def baseEnd_4784186 : Nat := 2456586958511124083972935

theorem tailTrace_4784186 : CollatzResearch.WordTrace tailWord_4784186 prefixEnd_4784186 2456586958511124083972935 := by
  unfold tailWord_4784186
  simp only [CollatzResearch.WordTrace]
  refine ⟨43623399661429667690833103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116329065763812447175554941 43623399661429667690833103)
  ·
    refine ⟨65435099492144501536249655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43623399661429667690833103 65435099492144501536249655)
    ·
      refine ⟨98152649238216752304374483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65435099492144501536249655 98152649238216752304374483)
      ·
        refine ⟨147228973857325128456561725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98152649238216752304374483 147228973857325128456561725)
        ·
          refine ⟨55210865196496923171210647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147228973857325128456561725 55210865196496923171210647)
          ·
            refine ⟨82816297794745384756815971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55210865196496923171210647 82816297794745384756815971)
            ·
              refine ⟨124224446692118077135223957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82816297794745384756815971 124224446692118077135223957)
              ·
                refine ⟨5823020938693034865713623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 124224446692118077135223957 5823020938693034865713623)
                ·
                  refine ⟨8734531408039552298570435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5823020938693034865713623 8734531408039552298570435)
                  ·
                    refine ⟨13101797112059328447855653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8734531408039552298570435 13101797112059328447855653)
                    ·
                      refine ⟨2456586958511124083972935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13101797112059328447855653 2456586958511124083972935)
                      ·
                        rfl

theorem cell23_4784186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6, 1, 1, 4].length) (baseStart_4784186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784186 prefixEnd_4784186 := by exact prefixLift 4784186
  have htrace : WordTrace (prefixWord ++ tailWord_4784186) baseStart_4784186 baseEnd_4784186 := by
    simpa [prefixWord, tailWord_4784186, baseEnd_4784186] using wordTrace_append hprefix tailTrace_4784186
  have hstable : (prefixWord ++ tailWord_4784186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784186).length < 2 ^ (prefixWord ++ tailWord_4784186).sum := by decide
  have hdescent : baseEnd_4784186 < baseStart_4784186 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784190 : List Nat := [4, 2, 1, 3, 2, 1, 1, 1, 1, 5, 2]
def baseStart_4784190 : Nat := 118140960795 + 4784190 * 2 ^ 59
def prefixEnd_4784190 : Nat := 4983230072969 + 3 ^ 40 * 4784190 * 2
def baseEnd_4784190 : Nat := 2456589012433742068322917

theorem tailTrace_4784190 : CollatzResearch.WordTrace tailWord_4784190 prefixEnd_4784190 2456589012433742068322917 := by
  unfold tailWord_4784190
  simp only [CollatzResearch.WordTrace]
  refine ⟨21811718067213022430809753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116329163025136119630985349 21811718067213022430809753)
  ·
    refine ⟨16358788550409766823107315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21811718067213022430809753 16358788550409766823107315)
    ·
      refine ⟨24538182825614650234660973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16358788550409766823107315 24538182825614650234660973)
      ·
        refine ⟨9201818559605493837997865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24538182825614650234660973 9201818559605493837997865)
        ·
          refine ⟨6901363919704120378498399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9201818559605493837997865 6901363919704120378498399)
          ·
            refine ⟨10352045879556180567747599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6901363919704120378498399 10352045879556180567747599)
            ·
              refine ⟨15528068819334270851621399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10352045879556180567747599 15528068819334270851621399)
              ·
                refine ⟨23292103229001406277432099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15528068819334270851621399 23292103229001406277432099)
                ·
                  refine ⟨34938154843502109416148149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23292103229001406277432099 34938154843502109416148149)
                  ·
                    refine ⟨3275452016578322757763889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34938154843502109416148149 3275452016578322757763889)
                    ·
                      refine ⟨2456589012433742068322917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3275452016578322757763889 2456589012433742068322917)
                      ·
                        rfl

theorem cell23_4784190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_4784190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784190 prefixEnd_4784190 := by exact prefixLift 4784190
  have htrace : WordTrace (prefixWord ++ tailWord_4784190) baseStart_4784190 baseEnd_4784190 := by
    simpa [prefixWord, tailWord_4784190, baseEnd_4784190] using wordTrace_append hprefix tailTrace_4784190
  have hstable : (prefixWord ++ tailWord_4784190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784190).length < 2 ^ (prefixWord ++ tailWord_4784190).sum := by decide
  have hdescent : baseEnd_4784190 < baseStart_4784190 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784213 : List Nat := [1, 3, 2, 2, 1, 3, 3, 2, 2, 4]
def baseStart_4784213 : Nat := 118140960795 + 4784213 * 2 ^ 59
def prefixEnd_4784213 : Nat := 4983230072969 + 3 ^ 40 * 4784213 * 2
def baseEnd_4784213 : Nat := 818866940829598492778437

theorem tailTrace_4784213 : CollatzResearch.WordTrace tailWord_4784213 prefixEnd_4784213 818866940829598492778437 := by
  unfold tailWord_4784213
  simp only [CollatzResearch.WordTrace]
  refine ⟨174494583416620854374565293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116329722277747236249710195 174494583416620854374565293)
  ·
    refine ⟨65435468781232820390461985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174494583416620854374565293 65435468781232820390461985)
    ·
      refine ⟨49076601585924615292846489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65435468781232820390461985 49076601585924615292846489)
      ·
        refine ⟨36807451189443461469634867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49076601585924615292846489 36807451189443461469634867)
        ·
          refine ⟨55211176784165192204452301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36807451189443461469634867 55211176784165192204452301)
          ·
            refine ⟨20704191294061947076669613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55211176784165192204452301 20704191294061947076669613)
            ·
              refine ⟨7764071735273230153751105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20704191294061947076669613 7764071735273230153751105)
              ·
                refine ⟨5823053801454922615313329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7764071735273230153751105 5823053801454922615313329)
                ·
                  refine ⟨4367290351091191961484997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5823053801454922615313329 4367290351091191961484997)
                  ·
                    refine ⟨818866940829598492778437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4367290351091191961484997 818866940829598492778437)
                    ·
                      rfl

theorem cell23_4784213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2, 2, 4].length) (baseStart_4784213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784213 prefixEnd_4784213 := by exact prefixLift 4784213
  have htrace : WordTrace (prefixWord ++ tailWord_4784213) baseStart_4784213 baseEnd_4784213 := by
    simpa [prefixWord, tailWord_4784213, baseEnd_4784213] using wordTrace_append hprefix tailTrace_4784213
  have hstable : (prefixWord ++ tailWord_4784213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784213).length < 2 ^ (prefixWord ++ tailWord_4784213).sum := by decide
  have hdescent : baseEnd_4784213 < baseStart_4784213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784214 : List Nat := [5, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3]
def baseStart_4784214 : Nat := 118140960795 + 4784214 * 2 ^ 59
def prefixEnd_4784214 : Nat := 4983230072969 + 3 ^ 40 * 4784214 * 2
def baseEnd_4784214 : Nat := 2456601335969449974422807

theorem tailTrace_4784214 : CollatzResearch.WordTrace tailWord_4784214 prefixEnd_4784214 2456601335969449974422807 := by
  unfold tailWord_4784214
  simp only [CollatzResearch.WordTrace]
  refine ⟨10905913743101076971584481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116329746593078154363567797 10905913743101076971584481)
  ·
    refine ⟨8179435307325807728688361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10905913743101076971584481 8179435307325807728688361)
    ·
      refine ⟨6134576480494355796516271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8179435307325807728688361 6134576480494355796516271)
      ·
        refine ⟨9201864720741533694774407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6134576480494355796516271 9201864720741533694774407)
        ·
          refine ⟨13802797081112300542161611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9201864720741533694774407 13802797081112300542161611)
          ·
            refine ⟨20704195621668450813242417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13802797081112300542161611 20704195621668450813242417)
            ·
              refine ⟨15528146716251338109931813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20704195621668450813242417 15528146716251338109931813)
              ·
                refine ⟨2911527509297125895612215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15528146716251338109931813 2911527509297125895612215)
                ·
                  refine ⟨4367291263945688843418323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2911527509297125895612215 4367291263945688843418323)
                  ·
                    refine ⟨6550936895918533265127485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4367291263945688843418323 6550936895918533265127485)
                    ·
                      refine ⟨2456601335969449974422807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6550936895918533265127485 2456601335969449974422807)
                      ·
                        rfl

theorem cell23_4784214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_4784214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784214 prefixEnd_4784214 := by exact prefixLift 4784214
  have htrace : WordTrace (prefixWord ++ tailWord_4784214) baseStart_4784214 baseEnd_4784214 := by
    simpa [prefixWord, tailWord_4784214, baseEnd_4784214] using wordTrace_append hprefix tailTrace_4784214
  have hstable : (prefixWord ++ tailWord_4784214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784214).length < 2 ^ (prefixWord ++ tailWord_4784214).sum := by decide
  have hdescent : baseEnd_4784214 < baseStart_4784214 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784220 : List Nat := [2, 2, 4, 1, 1, 2, 1, 3, 3, 2, 2]
def baseStart_4784220 : Nat := 118140960795 + 4784220 * 2 ^ 59
def prefixEnd_4784220 : Nat := 4983230072969 + 3 ^ 40 * 4784220 * 2
def baseEnd_4784220 : Nat := 2456604416853376950947779

theorem tailTrace_4784220 : CollatzResearch.WordTrace tailWord_4784220 prefixEnd_4784220 2456604416853376950947779 := by
  unfold tailWord_4784220
  simp only [CollatzResearch.WordTrace]
  refine ⟨87247419363797747285035057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116329892485063663046713409 87247419363797747285035057)
  ·
    refine ⟨65435564522848310463776293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87247419363797747285035057 65435564522848310463776293)
    ·
      refine ⟨12269168348034058211958055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65435564522848310463776293 12269168348034058211958055)
      ·
        refine ⟨18403752522051087317937083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12269168348034058211958055 18403752522051087317937083)
        ·
          refine ⟨27605628783076630976905625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18403752522051087317937083 27605628783076630976905625)
          ·
            refine ⟨20704221587307473232679219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27605628783076630976905625 20704221587307473232679219)
            ·
              refine ⟨31056332380961209849018829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20704221587307473232679219 31056332380961209849018829)
              ·
                refine ⟨11646124642860453693382061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31056332380961209849018829 11646124642860453693382061)
                ·
                  refine ⟨4367296741072670135018273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11646124642860453693382061 4367296741072670135018273)
                  ·
                    refine ⟨3275472555804502601263705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4367296741072670135018273 3275472555804502601263705)
                    ·
                      refine ⟨2456604416853376950947779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3275472555804502601263705 2456604416853376950947779)
                      ·
                        rfl

theorem cell23_4784220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_4784220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784220 prefixEnd_4784220 := by exact prefixLift 4784220
  have htrace : WordTrace (prefixWord ++ tailWord_4784220) baseStart_4784220 baseEnd_4784220 := by
    simpa [prefixWord, tailWord_4784220, baseEnd_4784220] using wordTrace_append hprefix tailTrace_4784220
  have hstable : (prefixWord ++ tailWord_4784220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784220).length < 2 ^ (prefixWord ++ tailWord_4784220).sum := by decide
  have hdescent : baseEnd_4784220 < baseStart_4784220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784253 : List Nat := [1, 4, 1, 1, 3, 2, 1, 2, 4, 1, 3]
def baseStart_4784253 : Nat := 118140960795 + 4784253 * 2 ^ 59
def prefixEnd_4784253 : Nat := 4983230072969 + 3 ^ 40 * 4784253 * 2
def baseEnd_4784253 : Nat := 2456621361714975321835127

theorem tailTrace_4784253 : CollatzResearch.WordTrace tailWord_4784253 prefixEnd_4784253 2456621361714975321835127 := by
  unfold tailWord_4784253
  simp only [CollatzResearch.WordTrace]
  refine ⟨174496042336475941206021413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116330694890983960804014275 174496042336475941206021413)
  ·
    refine ⟨32718007938089238976129015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174496042336475941206021413 32718007938089238976129015)
    ·
      refine ⟨49077011907133858464193523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32718007938089238976129015 49077011907133858464193523)
      ·
        refine ⟨73615517860700787696290285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49077011907133858464193523 73615517860700787696290285)
        ·
          refine ⟨27605819197762795386108857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73615517860700787696290285 27605819197762795386108857)
          ·
            refine ⟨20704364398322096539581643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27605819197762795386108857 20704364398322096539581643)
            ·
              refine ⟨31056546597483144809372465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20704364398322096539581643 31056546597483144809372465)
              ·
                refine ⟨23292409948112358607029349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31056546597483144809372465 23292409948112358607029349)
                ·
                  refine ⟨4367326865271067238818003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23292409948112358607029349 4367326865271067238818003)
                  ·
                    refine ⟨6550990297906600858227005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4367326865271067238818003 6550990297906600858227005)
                    ·
                      refine ⟨2456621361714975321835127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6550990297906600858227005 2456621361714975321835127)
                      ·
                        rfl

theorem cell23_4784253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 4, 1, 3].length) (baseStart_4784253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784253 prefixEnd_4784253 := by exact prefixLift 4784253
  have htrace : WordTrace (prefixWord ++ tailWord_4784253) baseStart_4784253 baseEnd_4784253 := by
    simpa [prefixWord, tailWord_4784253, baseEnd_4784253] using wordTrace_append hprefix tailTrace_4784253
  have hstable : (prefixWord ++ tailWord_4784253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784253).length < 2 ^ (prefixWord ++ tailWord_4784253).sum := by decide
  have hdescent : baseEnd_4784253 < baseStart_4784253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784287 : List Nat := [1, 1, 2, 6, 1, 1, 4, 1, 2, 1, 3]
def baseStart_4784287 : Nat := 118140960795 + 4784287 * 2 ^ 59
def prefixEnd_4784287 : Nat := 4983230072969 + 3 ^ 40 * 4784287 * 2
def baseEnd_4784287 : Nat := 2456638820057228188809971

theorem tailTrace_4784287 : CollatzResearch.WordTrace tailWord_4784287 prefixEnd_4784287 2456638820057228188809971 := by
  unfold tailWord_4784287
  simp only [CollatzResearch.WordTrace]
  refine ⟨174497282418352765012759115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116331521612235176675172743 174497282418352765012759115)
  ·
    refine ⟨261745923627529147519138673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174497282418352765012759115 261745923627529147519138673)
    ·
      refine ⟨196309442720646860639354005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261745923627529147519138673 196309442720646860639354005)
      ·
        refine ⟨9202005127530321592469719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 196309442720646860639354005 9202005127530321592469719)
        ·
          refine ⟨13803007691295482388704579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9202005127530321592469719 13803007691295482388704579)
          ·
            refine ⟨20704511536943223583056869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13803007691295482388704579 20704511536943223583056869)
            ·
              refine ⟨3882095913176854421823163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20704511536943223583056869 3882095913176854421823163)
              ·
                refine ⟨5823143869765281632734745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3882095913176854421823163 5823143869765281632734745)
                ·
                  refine ⟨4367357902323961224551059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5823143869765281632734745 4367357902323961224551059)
                  ·
                    refine ⟨6551036853485941836826589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4367357902323961224551059 6551036853485941836826589)
                    ·
                      refine ⟨2456638820057228188809971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6551036853485941836826589 2456638820057228188809971)
                      ·
                        rfl

theorem cell23_4784287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_4784287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784287 prefixEnd_4784287 := by exact prefixLift 4784287
  have htrace : WordTrace (prefixWord ++ tailWord_4784287) baseStart_4784287 baseEnd_4784287 := by
    simpa [prefixWord, tailWord_4784287, baseEnd_4784287] using wordTrace_append hprefix tailTrace_4784287
  have hstable : (prefixWord ++ tailWord_4784287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784287).length < 2 ^ (prefixWord ++ tailWord_4784287).sum := by decide
  have hdescent : baseEnd_4784287 < baseStart_4784287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784293 : List Nat := [1, 3, 1, 2, 1, 3, 2, 3, 1, 4, 2]
def baseStart_4784293 : Nat := 118140960795 + 4784293 * 2 ^ 59
def prefixEnd_4784293 : Nat := 4983230072969 + 3 ^ 40 * 4784293 * 2
def baseEnd_4784293 : Nat := 2456641900941155165334943

theorem tailTrace_4784293 : CollatzResearch.WordTrace tailWord_4784293 prefixEnd_4784293 2456641900941155165334943 := by
  unfold tailWord_4784293
  simp only [CollatzResearch.WordTrace]
  refine ⟨174497501256331028037477533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116331667504220685358318355 174497501256331028037477533)
  ·
    refine ⟨65436562971124135514054075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174497501256331028037477533 65436562971124135514054075)
    ·
      refine ⟨98154844456686203271081113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65436562971124135514054075 98154844456686203271081113)
      ·
        refine ⟨73616133342514652453310835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98154844456686203271081113 73616133342514652453310835)
        ·
          refine ⟨110424200013771978679966253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73616133342514652453310835 110424200013771978679966253)
          ·
            refine ⟨41409075005164492004987345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110424200013771978679966253 41409075005164492004987345)
            ·
              refine ⟨31056806253873369003740509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41409075005164492004987345 31056806253873369003740509)
              ·
                refine ⟨11646302345202513376402691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31056806253873369003740509 11646302345202513376402691)
                ·
                  refine ⟨17469453517803770064604037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11646302345202513376402691 17469453517803770064604037)
                  ·
                    refine ⟨3275522534588206887113257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17469453517803770064604037 3275522534588206887113257)
                    ·
                      refine ⟨2456641900941155165334943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3275522534588206887113257 2456641900941155165334943)
                      ·
                        rfl

theorem cell23_4784293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 4, 2].length) (baseStart_4784293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784293 prefixEnd_4784293 := by exact prefixLift 4784293
  have htrace : WordTrace (prefixWord ++ tailWord_4784293) baseStart_4784293 baseEnd_4784293 := by
    simpa [prefixWord, tailWord_4784293, baseEnd_4784293] using wordTrace_append hprefix tailTrace_4784293
  have hstable : (prefixWord ++ tailWord_4784293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784293).length < 2 ^ (prefixWord ++ tailWord_4784293).sum := by decide
  have hdescent : baseEnd_4784293 < baseStart_4784293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784346 : List Nat := [3, 1, 1, 2, 2, 1, 2, 2, 4, 5]
def baseStart_4784346 : Nat := 118140960795 + 4784346 * 2 ^ 59
def prefixEnd_4784346 : Nat := 4983230072969 + 3 ^ 40 * 4784346 * 2
def baseEnd_4784346 : Nat := 818889705138614485990733

theorem tailTrace_4784346 : CollatzResearch.WordTrace tailWord_4784346 prefixEnd_4784346 818889705138614485990733 := by
  unfold tailWord_4784346
  simp only [CollatzResearch.WordTrace]
  refine ⟨43624858581284754522289223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116332956216759345392771261 43624858581284754522289223)
  ·
    refine ⟨65437287871927131783433835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43624858581284754522289223 65437287871927131783433835)
    ·
      refine ⟨98155931807890697675150753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65437287871927131783433835 98155931807890697675150753)
      ·
        refine ⟨73616948855918023256363065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98155931807890697675150753 73616948855918023256363065)
        ·
          refine ⟨55212711641938517442272299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73616948855918023256363065 55212711641938517442272299)
          ·
            refine ⟨82819067462907776163408449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55212711641938517442272299 82819067462907776163408449)
            ·
              refine ⟨62114300597180832122556337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82819067462907776163408449 62114300597180832122556337)
              ·
                refine ⟨46585725447885624091917253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62114300597180832122556337 46585725447885624091917253)
                ·
                  refine ⟨8734823521478554517234485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46585725447885624091917253 8734823521478554517234485)
                  ·
                    refine ⟨818889705138614485990733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8734823521478554517234485 818889705138614485990733)
                    ·
                      rfl

theorem cell23_4784346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 4, 5].length) (baseStart_4784346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784346 prefixEnd_4784346 := by exact prefixLift 4784346
  have htrace : WordTrace (prefixWord ++ tailWord_4784346) baseStart_4784346 baseEnd_4784346 := by
    simpa [prefixWord, tailWord_4784346, baseEnd_4784346] using wordTrace_append hprefix tailTrace_4784346
  have hstable : (prefixWord ++ tailWord_4784346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784346).length < 2 ^ (prefixWord ++ tailWord_4784346).sum := by decide
  have hdescent : baseEnd_4784346 < baseStart_4784346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784353 : List Nat := [1, 2, 3, 1, 3, 1, 1, 2, 2, 5, 2]
def baseStart_4784353 : Nat := 118140960795 + 4784353 * 2 ^ 59
def prefixEnd_4784353 : Nat := 4983230072969 + 3 ^ 40 * 4784353 * 2
def baseEnd_4784353 : Nat := 2456672709780424930584667

theorem tailTrace_4784353 : CollatzResearch.WordTrace tailWord_4784353 prefixEnd_4784353 2456672709780424930584667 := by
  unfold tailWord_4784353
  simp only [CollatzResearch.WordTrace]
  refine ⟨174499689636113658284661713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116333126424075772189774475 174499689636113658284661713)
  ·
    refine ⟨130874767227085243713496285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174499689636113658284661713 130874767227085243713496285)
    ·
      refine ⟨49078037710156966392561107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130874767227085243713496285 49078037710156966392561107)
      ·
        refine ⟨73617056565235449588841661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49078037710156966392561107 73617056565235449588841661)
        ·
          refine ⟨27606396211963293595815623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73617056565235449588841661 27606396211963293595815623)
          ·
            refine ⟨41409594317944940393723435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27606396211963293595815623 41409594317944940393723435)
            ·
              refine ⟨62114391476917410590585153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41409594317944940393723435 62114391476917410590585153)
              ·
                refine ⟨46585793607688057942938865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62114391476917410590585153 46585793607688057942938865)
                ·
                  refine ⟨34939345205766043457204149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46585793607688057942938865 34939345205766043457204149)
                  ·
                    refine ⟨3275563613040566574112889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34939345205766043457204149 3275563613040566574112889)
                    ·
                      refine ⟨2456672709780424930584667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3275563613040566574112889 2456672709780424930584667)
                      ·
                        rfl

theorem cell23_4784353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 5, 2].length) (baseStart_4784353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784353 prefixEnd_4784353 := by exact prefixLift 4784353
  have htrace : WordTrace (prefixWord ++ tailWord_4784353) baseStart_4784353 baseEnd_4784353 := by
    simpa [prefixWord, tailWord_4784353, baseEnd_4784353] using wordTrace_append hprefix tailTrace_4784353
  have hstable : (prefixWord ++ tailWord_4784353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784353).length < 2 ^ (prefixWord ++ tailWord_4784353).sum := by decide
  have hdescent : baseEnd_4784353 < baseStart_4784353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784383 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 4, 4, 2]
def baseStart_4784383 : Nat := 118140960795 + 4784383 * 2 ^ 59
def prefixEnd_4784383 : Nat := 4983230072969 + 3 ^ 40 * 4784383 * 2
def baseEnd_4784383 : Nat := 2456688114200059813209529

theorem tailTrace_4784383 : CollatzResearch.WordTrace tailWord_4784383 prefixEnd_4784383 2456688114200059813209529 := by
  unfold tailWord_4784383
  simp only [CollatzResearch.WordTrace]
  refine ⟨174500783826004973408253803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116333855884003315605502535 174500783826004973408253803)
  ·
    refine ⟨261751175739007460112380705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174500783826004973408253803 261751175739007460112380705)
    ·
      refine ⟨196313381804255595084285529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261751175739007460112380705 196313381804255595084285529)
      ·
        refine ⟨147235036353191696313214147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196313381804255595084285529 147235036353191696313214147)
        ·
          refine ⟨220852554529787544469821221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147235036353191696313214147 220852554529787544469821221)
          ·
            refine ⟨41409853974335164588091479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 220852554529787544469821221 41409853974335164588091479)
            ·
              refine ⟨62114780961502746882137219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41409853974335164588091479 62114780961502746882137219)
              ·
                refine ⟨93172171442254120323205829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62114780961502746882137219 93172171442254120323205829)
                ·
                  refine ⟨17469782145422647560601093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93172171442254120323205829 17469782145422647560601093)
                  ·
                    refine ⟨3275584152266746417612705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17469782145422647560601093 3275584152266746417612705)
                    ·
                      refine ⟨2456688114200059813209529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3275584152266746417612705 2456688114200059813209529)
                      ·
                        rfl

theorem cell23_4784383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 4, 2].length) (baseStart_4784383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784383 prefixEnd_4784383 := by exact prefixLift 4784383
  have htrace : WordTrace (prefixWord ++ tailWord_4784383) baseStart_4784383 baseEnd_4784383 := by
    simpa [prefixWord, tailWord_4784383, baseEnd_4784383] using wordTrace_append hprefix tailTrace_4784383
  have hstable : (prefixWord ++ tailWord_4784383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784383).length < 2 ^ (prefixWord ++ tailWord_4784383).sum := by decide
  have hdescent : baseEnd_4784383 < baseStart_4784383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784393 : List Nat := [1, 2, 1, 1, 3, 4, 1, 3, 3, 4]
def baseStart_4784393 : Nat := 118140960795 + 4784393 * 2 ^ 59
def prefixEnd_4784393 : Nat := 4983230072969 + 3 ^ 40 * 4784393 * 2
def baseEnd_4784393 : Nat := 818897749668868258028161

theorem tailTrace_4784393 : CollatzResearch.WordTrace tailWord_4784393 prefixEnd_4784393 818897749668868258028161 := by
  unfold tailWord_4784393
  simp only [CollatzResearch.WordTrace]
  refine ⟨174501148555968745116117833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116334099037312496744078555 174501148555968745116117833)
  ·
    refine ⟨130875861416976558837088375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174501148555968745116117833 130875861416976558837088375)
    ·
      refine ⟨196313792125464838255632563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130875861416976558837088375 196313792125464838255632563)
      ·
        refine ⟨294470688188197257383448845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196313792125464838255632563 294470688188197257383448845)
        ·
          refine ⟨110426508070573971518793317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 294470688188197257383448845 110426508070573971518793317)
          ·
            refine ⟨20704970263232619659773747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110426508070573971518793317 20704970263232619659773747)
            ·
              refine ⟨31057455394848929489660621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20704970263232619659773747 31057455394848929489660621)
              ·
                refine ⟨11646545773068348558622733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31057455394848929489660621 11646545773068348558622733)
                ·
                  refine ⟨4367454664900630709483525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11646545773068348558622733 4367454664900630709483525)
                  ·
                    refine ⟨818897749668868258028161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4367454664900630709483525 818897749668868258028161)
                    ·
                      rfl

theorem cell23_4784393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 3, 4].length) (baseStart_4784393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784393 prefixEnd_4784393 := by exact prefixLift 4784393
  have htrace : WordTrace (prefixWord ++ tailWord_4784393) baseStart_4784393 baseEnd_4784393 := by
    simpa [prefixWord, tailWord_4784393, baseEnd_4784393] using wordTrace_append hprefix tailTrace_4784393
  have hstable : (prefixWord ++ tailWord_4784393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784393).length < 2 ^ (prefixWord ++ tailWord_4784393).sum := by decide
  have hdescent : baseEnd_4784393 < baseStart_4784393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784396 : List Nat := [2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 6]
def baseStart_4784396 : Nat := 118140960795 + 4784396 * 2 ^ 59
def prefixEnd_4784396 : Nat := 4983230072969 + 3 ^ 40 * 4784396 * 2
def baseEnd_4784396 : Nat := 2456694789448568262346969

theorem tailTrace_4784396 : CollatzResearch.WordTrace tailWord_4784396 prefixEnd_4784396 2456694789448568262346969 := by
  unfold tailWord_4784396
  simp only [CollatzResearch.WordTrace]
  refine ⟨87250628987478938314238521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116334171983305251085651361 87250628987478938314238521)
  ·
    refine ⟨65437971740609203735678891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87250628987478938314238521 65437971740609203735678891)
    ·
      refine ⟨98156957610913805603518337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65437971740609203735678891 98156957610913805603518337)
      ·
        refine ⟨73617718208185354202638753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98156957610913805603518337 73617718208185354202638753)
        ·
          refine ⟨55213288656139015651979065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73617718208185354202638753 55213288656139015651979065)
          ·
            refine ⟨41409966492104261738984299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55213288656139015651979065 41409966492104261738984299)
            ·
              refine ⟨62114949738156392608476449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41409966492104261738984299 62114949738156392608476449)
              ·
                refine ⟨46586212303617294456357337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62114949738156392608476449 46586212303617294456357337)
                ·
                  refine ⟨34939659227712970842268003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46586212303617294456357337 34939659227712970842268003)
                  ·
                    refine ⟨52409488841569456263402005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34939659227712970842268003 52409488841569456263402005)
                    ·
                      refine ⟨2456694789448568262346969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52409488841569456263402005 2456694789448568262346969)
                      ·
                        rfl

theorem cell23_4784396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_4784396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784396 prefixEnd_4784396 := by exact prefixLift 4784396
  have htrace : WordTrace (prefixWord ++ tailWord_4784396) baseStart_4784396 baseEnd_4784396 := by
    simpa [prefixWord, tailWord_4784396, baseEnd_4784396] using wordTrace_append hprefix tailTrace_4784396
  have hstable : (prefixWord ++ tailWord_4784396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784396).length < 2 ^ (prefixWord ++ tailWord_4784396).sum := by decide
  have hdescent : baseEnd_4784396 < baseStart_4784396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784460 : List Nat := [2, 2, 1, 3, 2, 1, 1, 2, 4, 3, 2]
def baseStart_4784460 : Nat := 118140960795 + 4784460 * 2 ^ 59
def prefixEnd_4784460 : Nat := 4983230072969 + 3 ^ 40 * 4784460 * 2
def baseEnd_4784460 : Nat := 2456727652210456011946675

theorem tailTrace_4784460 : CollatzResearch.WordTrace tailWord_4784460 prefixEnd_4784460 2456727652210456011946675 := by
  unfold tailWord_4784460
  simp only [CollatzResearch.WordTrace]
  refine ⟨87251796123363007779403417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116335728164484010372537889 87251796123363007779403417)
  ·
    refine ⟨65438847092522255834552563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87251796123363007779403417 65438847092522255834552563)
    ·
      refine ⟨98158270638783383751828845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65438847092522255834552563 98158270638783383751828845)
      ·
        refine ⟨36809351489543768906935817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98158270638783383751828845 36809351489543768906935817)
        ·
          refine ⟨27607013617157826680201863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36809351489543768906935817 27607013617157826680201863)
          ·
            refine ⟨41410520425736740020302795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27607013617157826680201863 41410520425736740020302795)
            ·
              refine ⟨62115780638605110030454193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41410520425736740020302795 62115780638605110030454193)
              ·
                refine ⟨46586835478953832522840645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62115780638605110030454193 46586835478953832522840645)
                ·
                  refine ⟨8735031652303843598032621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46586835478953832522840645 8735031652303843598032621)
                  ·
                    refine ⟨3275636869613941349262233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8735031652303843598032621 3275636869613941349262233)
                    ·
                      refine ⟨2456727652210456011946675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3275636869613941349262233 2456727652210456011946675)
                      ·
                        rfl

theorem cell23_4784460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 4, 3, 2].length) (baseStart_4784460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784460 prefixEnd_4784460 := by exact prefixLift 4784460
  have htrace : WordTrace (prefixWord ++ tailWord_4784460) baseStart_4784460 baseEnd_4784460 := by
    simpa [prefixWord, tailWord_4784460, baseEnd_4784460] using wordTrace_append hprefix tailTrace_4784460
  have hstable : (prefixWord ++ tailWord_4784460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784460).length < 2 ^ (prefixWord ++ tailWord_4784460).sum := by decide
  have hdescent : baseEnd_4784460 < baseStart_4784460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784483 : List Nat := [1, 1, 1, 5, 2, 1, 3, 2, 1, 6]
def baseStart_4784483 : Nat := 118140960795 + 4784483 * 2 ^ 59
def prefixEnd_4784483 : Nat := 4983230072969 + 3 ^ 40 * 4784483 * 2
def baseEnd_4784483 : Nat := 818913154088503140653023

theorem tailTrace_4784483 : CollatzResearch.WordTrace tailWord_4784483 prefixEnd_4784483 818913154088503140653023 := by
  unfold tailWord_4784483
  simp only [CollatzResearch.WordTrace]
  refine ⟨174504431125642690486894103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116336287417095126991262735 174504431125642690486894103)
  ·
    refine ⟨261756646688464035730341155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174504431125642690486894103 261756646688464035730341155)
    ·
      refine ⟨392634970032696053595511733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261756646688464035730341155 392634970032696053595511733)
      ·
        refine ⟨36809528440565255024579225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 392634970032696053595511733 36809528440565255024579225)
        ·
          refine ⟨27607146330423941268434419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36809528440565255024579225 27607146330423941268434419)
          ·
            refine ⟨41410719495635911902651629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27607146330423941268434419 41410719495635911902651629)
            ·
              refine ⟨15529019810863466963494361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41410719495635911902651629 15529019810863466963494361)
              ·
                refine ⟨11646764858147600222620771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15529019810863466963494361 11646764858147600222620771)
                ·
                  refine ⟨17470147287221400333931157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11646764858147600222620771 17470147287221400333931157)
                  ·
                    refine ⟨818913154088503140653023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17470147287221400333931157 818913154088503140653023)
                    ·
                      rfl

theorem cell23_4784483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 6].length) (baseStart_4784483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784483 prefixEnd_4784483 := by exact prefixLift 4784483
  have htrace : WordTrace (prefixWord ++ tailWord_4784483) baseStart_4784483 baseEnd_4784483 := by
    simpa [prefixWord, tailWord_4784483, baseEnd_4784483] using wordTrace_append hprefix tailTrace_4784483
  have hstable : (prefixWord ++ tailWord_4784483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784483).length < 2 ^ (prefixWord ++ tailWord_4784483).sum := by decide
  have hdescent : baseEnd_4784483 < baseStart_4784483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784487 : List Nat := [1, 1, 5, 1, 3, 2, 3, 1, 1, 5]
def baseStart_4784487 : Nat := 118140960795 + 4784487 * 2 ^ 59
def prefixEnd_4784487 : Nat := 4983230072969 + 3 ^ 40 * 4784487 * 2
def baseEnd_4784487 : Nat := 818913838729375802103017

theorem tailTrace_4784487 : CollatzResearch.WordTrace tailWord_4784487 prefixEnd_4784487 818913838729375802103017 := by
  unfold tailWord_4784487
  simp only [CollatzResearch.WordTrace]
  refine ⟨174504577017628199170039715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116336384678418799446693143 174504577017628199170039715)
  ·
    refine ⟨261756865526442298755059573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174504577017628199170039715 261756865526442298755059573)
    ·
      refine ⟨24539706143103965508286835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 261756865526442298755059573 24539706143103965508286835)
      ·
        refine ⟨36809559214655948262430253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24539706143103965508286835 36809559214655948262430253)
        ·
          refine ⟨13803584705495980598411345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36809559214655948262430253 13803584705495980598411345)
          ·
            refine ⟨10352688529121985448808509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13803584705495980598411345 10352688529121985448808509)
            ·
              refine ⟨3882258198420744543303191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10352688529121985448808509 3882258198420744543303191)
              ·
                refine ⟨5823387297631116814954787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3882258198420744543303191 5823387297631116814954787)
                ·
                  refine ⟨8735080946446675222432181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5823387297631116814954787 8735080946446675222432181)
                  ·
                    refine ⟨818913838729375802103017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8735080946446675222432181 818913838729375802103017)
                    ·
                      rfl

theorem cell23_4784487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_4784487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784487 prefixEnd_4784487 := by exact prefixLift 4784487
  have htrace : WordTrace (prefixWord ++ tailWord_4784487) baseStart_4784487 baseEnd_4784487 := by
    simpa [prefixWord, tailWord_4784487, baseEnd_4784487] using wordTrace_append hprefix tailTrace_4784487
  have hstable : (prefixWord ++ tailWord_4784487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784487).length < 2 ^ (prefixWord ++ tailWord_4784487).sum := by decide
  have hdescent : baseEnd_4784487 < baseStart_4784487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784496 : List Nat := [2, 1, 1, 1, 4, 14]
def baseStart_4784496 : Nat := 118140960795 + 4784496 * 2 ^ 59
def prefixEnd_4784496 : Nat := 4983230072969 + 3 ^ 40 * 4784496 * 2
def baseEnd_4784496 : Nat := 10110066409522707288463

theorem tailTrace_4784496 : CollatzResearch.WordTrace tailWord_4784496 prefixEnd_4784496 10110066409522707288463 := by
  unfold tailWord_4784496
  simp only [CollatzResearch.WordTrace]
  refine ⟨87252452637297796853558671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116336603516397062471411561 87252452637297796853558671)
  ·
    refine ⟨130878678955946695280338007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87252452637297796853558671 130878678955946695280338007)
    ·
      refine ⟨196318018433920042920507011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130878678955946695280338007 196318018433920042920507011)
      ·
        refine ⟨294477027650880064380760517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196318018433920042920507011 294477027650880064380760517)
        ·
          refine ⟨55214442684540012071392597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 294477027650880064380760517 55214442684540012071392597)
          ·
            refine ⟨10110066409522707288463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 55214442684540012071392597 10110066409522707288463)
            ·
              rfl

theorem cell23_4784496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 14].length) (baseStart_4784496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784496 prefixEnd_4784496 := by exact prefixLift 4784496
  have htrace : WordTrace (prefixWord ++ tailWord_4784496) baseStart_4784496 baseEnd_4784496 := by
    simpa [prefixWord, tailWord_4784496, baseEnd_4784496] using wordTrace_append hprefix tailTrace_4784496
  have hstable : (prefixWord ++ tailWord_4784496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784496).length < 2 ^ (prefixWord ++ tailWord_4784496).sum := by decide
  have hdescent : baseEnd_4784496 < baseStart_4784496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784501 : List Nat := [1, 3, 4, 1, 2, 1, 4, 2, 1, 1, 3]
def baseStart_4784501 : Nat := 118140960795 + 4784501 * 2 ^ 59
def prefixEnd_4784501 : Nat := 4983230072969 + 3 ^ 40 * 4784501 * 2
def baseEnd_4784501 : Nat := 2456748704917290351533987

theorem tailTrace_4784501 : CollatzResearch.WordTrace tailWord_4784501 prefixEnd_4784501 2456748704917290351533987 := by
  unfold tailWord_4784501
  simp only [CollatzResearch.WordTrace]
  refine ⟨174505087639577479561049357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116336725093051653040699571 174505087639577479561049357)
  ·
    refine ⟨65439407864841554835393509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174505087639577479561049357 65439407864841554835393509)
    ·
      refine ⟨12269888974657791531636283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65439407864841554835393509 12269888974657791531636283)
      ·
        refine ⟨18404833461986687297454425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12269888974657791531636283 18404833461986687297454425)
        ·
          refine ⟨13803625096490015473090819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18404833461986687297454425 13803625096490015473090819)
          ·
            refine ⟨20705437644735023209636229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13803625096490015473090819 20705437644735023209636229)
            ·
              refine ⟨3882269558387816851806793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20705437644735023209636229 3882269558387816851806793)
              ·
                refine ⟨2911702168790862638855095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3882269558387816851806793 2911702168790862638855095)
                ·
                  refine ⟨4367553253186293958282643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2911702168790862638855095 4367553253186293958282643)
                  ·
                    refine ⟨6551329879779440937423965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4367553253186293958282643 6551329879779440937423965)
                    ·
                      refine ⟨2456748704917290351533987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6551329879779440937423965 2456748704917290351533987)
                      ·
                        rfl

theorem cell23_4784501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_4784501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784501 prefixEnd_4784501 := by exact prefixLift 4784501
  have htrace : WordTrace (prefixWord ++ tailWord_4784501) baseStart_4784501 baseEnd_4784501 := by
    simpa [prefixWord, tailWord_4784501, baseEnd_4784501] using wordTrace_append hprefix tailTrace_4784501
  have hstable : (prefixWord ++ tailWord_4784501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784501).length < 2 ^ (prefixWord ++ tailWord_4784501).sum := by decide
  have hdescent : baseEnd_4784501 < baseStart_4784501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784520 : List Nat := [2, 1, 3, 3, 1, 1, 4, 1, 1, 2, 4]
def baseStart_4784520 : Nat := 118140960795 + 4784520 * 2 ^ 59
def prefixEnd_4784520 : Nat := 4983230072969 + 3 ^ 40 * 4784520 * 2
def baseEnd_4784520 : Nat := 2456758461049725777196399

theorem tailTrace_4784520 : CollatzResearch.WordTrace tailWord_4784520 prefixEnd_4784520 2456758461049725777196399 := by
  unfold tailWord_4784520
  simp only [CollatzResearch.WordTrace]
  refine ⟨87252890313254322902995507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116337187084339097203994009 87252890313254322902995507)
  ·
    refine ⟨130879335469881484354493261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87252890313254322902995507 130879335469881484354493261)
    ·
      refine ⟨49079750801205556632934973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130879335469881484354493261 49079750801205556632934973)
      ·
        refine ⟨18404906550452083737350615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49079750801205556632934973 18404906550452083737350615)
        ·
          refine ⟨27607359825678125606025923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18404906550452083737350615 27607359825678125606025923)
          ·
            refine ⟨41411039738517188409038885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27607359825678125606025923 41411039738517188409038885)
            ·
              refine ⟨7764569950971972826694791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41411039738517188409038885 7764569950971972826694791)
              ·
                refine ⟨11646854926457959240042187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7764569950971972826694791 11646854926457959240042187)
                ·
                  refine ⟨17470282389686938860063281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11646854926457959240042187 17470282389686938860063281)
                  ·
                    refine ⟨13102711792265204145047461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17470282389686938860063281 13102711792265204145047461)
                    ·
                      refine ⟨2456758461049725777196399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13102711792265204145047461 2456758461049725777196399)
                      ·
                        rfl

theorem cell23_4784520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_4784520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784520 prefixEnd_4784520 := by exact prefixLift 4784520
  have htrace : WordTrace (prefixWord ++ tailWord_4784520) baseStart_4784520 baseEnd_4784520 := by
    simpa [prefixWord, tailWord_4784520, baseEnd_4784520] using wordTrace_append hprefix tailTrace_4784520
  have hstable : (prefixWord ++ tailWord_4784520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784520).length < 2 ^ (prefixWord ++ tailWord_4784520).sum := by decide
  have hdescent : baseEnd_4784520 < baseStart_4784520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784541 : List Nat := [1, 4, 2, 1, 5, 1, 2, 1, 1, 1, 4]
def baseStart_4784541 : Nat := 118140960795 + 4784541 * 2 ^ 59
def prefixEnd_4784541 : Nat := 4983230072969 + 3 ^ 40 * 4784541 * 2
def baseEnd_4784541 : Nat := 2456769244143470195033803

theorem tailTrace_4784541 : CollatzResearch.WordTrace tailWord_4784541 prefixEnd_4784541 2456769244143470195033803 := by
  unfold tailWord_4784541
  simp only [CollatzResearch.WordTrace]
  refine ⟨174506546559432566392505477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116337697706288377595003651 174506546559432566392505477)
  ·
    refine ⟨32719977479893606198594777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174506546559432566392505477 32719977479893606198594777)
    ·
      refine ⟨24539983109920204648946083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32719977479893606198594777 24539983109920204648946083)
      ·
        refine ⟨36809974664880306973419125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24539983109920204648946083 36809974664880306973419125)
        ·
          refine ⟨3450935124832528778758043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36809974664880306973419125 3450935124832528778758043)
          ·
            refine ⟨5176402687248793168137065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3450935124832528778758043 5176402687248793168137065)
            ·
              refine ⟨3882302015436594876102799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5176402687248793168137065 3882302015436594876102799)
              ·
                refine ⟨5823453023154892314154199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3882302015436594876102799 5823453023154892314154199)
                ·
                  refine ⟨8735179534732338471231299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5823453023154892314154199 8735179534732338471231299)
                  ·
                    refine ⟨13102769302098507706846949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8735179534732338471231299 13102769302098507706846949)
                    ·
                      refine ⟨2456769244143470195033803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13102769302098507706846949 2456769244143470195033803)
                      ·
                        rfl

theorem cell23_4784541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 1, 1, 1, 4].length) (baseStart_4784541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784541 prefixEnd_4784541 := by exact prefixLift 4784541
  have htrace : WordTrace (prefixWord ++ tailWord_4784541) baseStart_4784541 baseEnd_4784541 := by
    simpa [prefixWord, tailWord_4784541, baseEnd_4784541] using wordTrace_append hprefix tailTrace_4784541
  have hstable : (prefixWord ++ tailWord_4784541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784541).length < 2 ^ (prefixWord ++ tailWord_4784541).sum := by decide
  have hdescent : baseEnd_4784541 < baseStart_4784541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784544 : List Nat := [2, 1, 1, 4, 1, 5, 2, 1, 1, 2, 3]
def baseStart_4784544 : Nat := 118140960795 + 4784544 * 2 ^ 59
def prefixEnd_4784544 : Nat := 4983230072969 + 3 ^ 40 * 4784544 * 2
def baseEnd_4784544 : Nat := 2456770784585433683296289

theorem tailTrace_4784544 : CollatzResearch.WordTrace tailWord_4784544 prefixEnd_4784544 2456770784585433683296289 := by
  unfold tailWord_4784544
  simp only [CollatzResearch.WordTrace]
  refine ⟨87253327989210848952432343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116337770652281131936576457 87253327989210848952432343)
  ·
    refine ⟨130879991983816273428648515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87253327989210848952432343 130879991983816273428648515)
    ·
      refine ⟨196319987975724410142972773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130879991983816273428648515 196319987975724410142972773)
      ·
        refine ⟨36809997745448326901807395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 196319987975724410142972773 36809997745448326901807395)
        ·
          refine ⟨55214996618172490352711093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36809997745448326901807395 55214996618172490352711093)
          ·
            refine ⟨5176405932953670970566665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55214996618172490352711093 5176405932953670970566665)
            ·
              refine ⟨3882304449715253227924999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5176405932953670970566665 3882304449715253227924999)
              ·
                refine ⟨5823456674572879841887499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3882304449715253227924999 5823456674572879841887499)
                ·
                  refine ⟨8735185011859319762831249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5823456674572879841887499 8735185011859319762831249)
                  ·
                    refine ⟨6551388758894489822123437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8735185011859319762831249 6551388758894489822123437)
                    ·
                      refine ⟨2456770784585433683296289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6551388758894489822123437 2456770784585433683296289)
                      ·
                        rfl

theorem cell23_4784544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 1, 1, 2, 3].length) (baseStart_4784544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784544 prefixEnd_4784544 := by exact prefixLift 4784544
  have htrace : WordTrace (prefixWord ++ tailWord_4784544) baseStart_4784544 baseEnd_4784544 := by
    simpa [prefixWord, tailWord_4784544, baseEnd_4784544] using wordTrace_append hprefix tailTrace_4784544
  have hstable : (prefixWord ++ tailWord_4784544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784544).length < 2 ^ (prefixWord ++ tailWord_4784544).sum := by decide
  have hdescent : baseEnd_4784544 < baseStart_4784544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784584 : List Nat := [2, 1, 3, 1, 3, 3, 2, 2, 1, 3, 2]
def baseStart_4784584 : Nat := 118140960795 + 4784584 * 2 ^ 59
def prefixEnd_4784584 : Nat := 4983230072969 + 3 ^ 40 * 4784584 * 2
def baseEnd_4784584 : Nat := 2456791323811613526796105

theorem tailTrace_4784584 : CollatzResearch.WordTrace tailWord_4784584 prefixEnd_4784584 2456791323811613526796105 := by
  unfold tailWord_4784584
  simp only [CollatzResearch.WordTrace]
  refine ⟨87254057449138392368160403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116338743265517856490880537 87254057449138392368160403)
  ·
    refine ⟨130881086173707588552240605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87254057449138392368160403 130881086173707588552240605)
    ·
      refine ⟨49080407315140345707090227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130881086173707588552240605 49080407315140345707090227)
      ·
        refine ⟨73620610972710518560635341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49080407315140345707090227 73620610972710518560635341)
        ·
          refine ⟨27607729114766444460238253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73620610972710518560635341 27607729114766444460238253)
          ·
            refine ⟨10352898418037416672589345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27607729114766444460238253 10352898418037416672589345)
            ·
              refine ⟨7764673813528062504442009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10352898418037416672589345 7764673813528062504442009)
              ·
                refine ⟨5823505360146046878331507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7764673813528062504442009 5823505360146046878331507)
                ·
                  refine ⟨8735258040219070317497261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5823505360146046878331507 8735258040219070317497261)
                  ·
                    refine ⟨3275721765082151369061473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8735258040219070317497261 3275721765082151369061473)
                    ·
                      refine ⟨2456791323811613526796105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3275721765082151369061473 2456791323811613526796105)
                      ·
                        rfl

theorem cell23_4784584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2, 1, 3, 2].length) (baseStart_4784584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784584 prefixEnd_4784584 := by exact prefixLift 4784584
  have htrace : WordTrace (prefixWord ++ tailWord_4784584) baseStart_4784584 baseEnd_4784584 := by
    simpa [prefixWord, tailWord_4784584, baseEnd_4784584] using wordTrace_append hprefix tailTrace_4784584
  have hstable : (prefixWord ++ tailWord_4784584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784584).length < 2 ^ (prefixWord ++ tailWord_4784584).sum := by decide
  have hdescent : baseEnd_4784584 < baseStart_4784584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784593 : List Nat := [1, 2, 2, 1, 2, 1, 1, 4, 1, 4, 4]
def baseStart_4784593 : Nat := 118140960795 + 4784593 * 2 ^ 59
def prefixEnd_4784593 : Nat := 4983230072969 + 3 ^ 40 * 4784593 * 2
def baseEnd_4784593 : Nat := 2456795945137503991583563

theorem tailTrace_4784593 : CollatzResearch.WordTrace tailWord_4784593 prefixEnd_4784593 2456795945137503991583563 := by
  unfold tailWord_4784593
  simp only [CollatzResearch.WordTrace]
  refine ⟨174508443155244179273398433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116338962103496119515598955 174508443155244179273398433)
  ·
    refine ⟨130881332366433134455048825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174508443155244179273398433 130881332366433134455048825)
    ·
      refine ⟨98160999274824850841286619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130881332366433134455048825 98160999274824850841286619)
      ·
        refine ⟨147241498912237276261929929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98160999274824850841286619 147241498912237276261929929)
        ·
          refine ⟨110431124184177957196447447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147241498912237276261929929 110431124184177957196447447)
          ·
            refine ⟨165646686276266935794671171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110431124184177957196447447 165646686276266935794671171)
            ·
              refine ⟨248470029414400403692006757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165646686276266935794671171 248470029414400403692006757)
              ·
                refine ⟨46588130515200075692251267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 248470029414400403692006757 46588130515200075692251267)
                ·
                  refine ⟨69882195772800113538376901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46588130515200075692251267 69882195772800113538376901)
                  ·
                    refine ⟨13102911707400021288445669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 69882195772800113538376901 13102911707400021288445669)
                    ·
                      refine ⟨2456795945137503991583563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13102911707400021288445669 2456795945137503991583563)
                      ·
                        rfl

theorem cell23_4784593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 4, 4].length) (baseStart_4784593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784593 prefixEnd_4784593 := by exact prefixLift 4784593
  have htrace : WordTrace (prefixWord ++ tailWord_4784593) baseStart_4784593 baseEnd_4784593 := by
    simpa [prefixWord, tailWord_4784593, baseEnd_4784593] using wordTrace_append hprefix tailTrace_4784593
  have hstable : (prefixWord ++ tailWord_4784593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784593).length < 2 ^ (prefixWord ++ tailWord_4784593).sum := by decide
  have hdescent : baseEnd_4784593 < baseStart_4784593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784633 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 3, 7]
def baseStart_4784633 : Nat := 118140960795 + 4784633 * 2 ^ 59
def prefixEnd_4784633 : Nat := 4983230072969 + 3 ^ 40 * 4784633 * 2
def baseEnd_4784633 : Nat := 818938828121227945027793

theorem tailTrace_4784633 : CollatzResearch.WordTrace tailWord_4784633 prefixEnd_4784633 818938828121227945027793 := by
  unfold tailWord_4784633
  simp only [CollatzResearch.WordTrace]
  refine ⟨174509902075099266104854553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116339934716732844069903035 174509902075099266104854553)
  ·
    refine ⟨130882426556324449578640915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174509902075099266104854553 130882426556324449578640915)
    ·
      refine ⟨196323639834486674367961373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130882426556324449578640915 196323639834486674367961373)
      ·
        refine ⟨73621364937932502887985515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196323639834486674367961373 73621364937932502887985515)
        ·
          refine ⟨110432047406898754331978273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73621364937932502887985515 110432047406898754331978273)
          ·
            refine ⟨82824035555174065748983705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110432047406898754331978273 82824035555174065748983705)
            ·
              refine ⟨62118026666380549311737779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82824035555174065748983705 62118026666380549311737779)
              ·
                refine ⟨93177039999570823967606669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62118026666380549311737779 93177039999570823967606669)
                ·
                  refine ⟨34941389999839058987852501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93177039999570823967606669 34941389999839058987852501)
                  ·
                    refine ⟨818938828121227945027793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34941389999839058987852501 818938828121227945027793)
                    ·
                      rfl

theorem cell23_4784633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 7].length) (baseStart_4784633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784633 prefixEnd_4784633 := by exact prefixLift 4784633
  have htrace : WordTrace (prefixWord ++ tailWord_4784633) baseStart_4784633 baseEnd_4784633 := by
    simpa [prefixWord, tailWord_4784633, baseEnd_4784633] using wordTrace_append hprefix tailTrace_4784633
  have hstable : (prefixWord ++ tailWord_4784633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784633).length < 2 ^ (prefixWord ++ tailWord_4784633).sum := by decide
  have hdescent : baseEnd_4784633 < baseStart_4784633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784643 : List Nat := [1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 7]
def baseStart_4784643 : Nat := 118140960795 + 4784643 * 2 ^ 59
def prefixEnd_4784643 : Nat := 4983230072969 + 3 ^ 40 * 4784643 * 2
def baseEnd_4784643 : Nat := 2456821619170228795958333

theorem tailTrace_4784643 : CollatzResearch.WordTrace tailWord_4784643 prefixEnd_4784643 2456821619170228795958333 := by
  unfold tailWord_4784643
  simp only [CollatzResearch.WordTrace]
  refine ⟨174510266805063037812718583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116340177870042025208479055 174510266805063037812718583)
  ·
    refine ⟨261765400207594556719077875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174510266805063037812718583 261765400207594556719077875)
    ·
      refine ⟨392648100311391835078616813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261765400207594556719077875 392648100311391835078616813)
      ·
        refine ⟨147243037616771938154481305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 392648100311391835078616813 147243037616771938154481305)
        ·
          refine ⟨110432278212578953615860979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147243037616771938154481305 110432278212578953615860979)
          ·
            refine ⟨165648417318868430423791469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110432278212578953615860979 165648417318868430423791469)
            ·
              refine ⟨62118156494575661408921801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 165648417318868430423791469 62118156494575661408921801)
              ·
                refine ⟨46588617370931746056691351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62118156494575661408921801 46588617370931746056691351)
                ·
                  refine ⟨69882926056397619085037027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46588617370931746056691351 69882926056397619085037027)
                  ·
                    refine ⟨104824389084596428627555541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69882926056397619085037027 104824389084596428627555541)
                    ·
                      refine ⟨2456821619170228795958333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 104824389084596428627555541 2456821619170228795958333)
                      ·
                        rfl

theorem cell23_4784643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_4784643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784643 prefixEnd_4784643 := by exact prefixLift 4784643
  have htrace : WordTrace (prefixWord ++ tailWord_4784643) baseStart_4784643 baseEnd_4784643 := by
    simpa [prefixWord, tailWord_4784643, baseEnd_4784643] using wordTrace_append hprefix tailTrace_4784643
  have hstable : (prefixWord ++ tailWord_4784643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784643).length < 2 ^ (prefixWord ++ tailWord_4784643).sum := by decide
  have hdescent : baseEnd_4784643 < baseStart_4784643 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784697 : List Nat := [1, 2, 1, 5, 1, 1, 3, 2, 3, 4]
def baseStart_4784697 : Nat := 118140960795 + 4784697 * 2 ^ 59
def prefixEnd_4784697 : Nat := 4983230072969 + 3 ^ 40 * 4784697 * 2
def baseEnd_4784697 : Nat := 818949782375190528227695

theorem tailTrace_4784697 : CollatzResearch.WordTrace tailWord_4784697 prefixEnd_4784697 818949782375190528227695 := by
  unfold tailWord_4784697
  simp only [CollatzResearch.WordTrace]
  refine ⟨174512236346867405035184345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116341490897911603356789563 174512236346867405035184345)
  ·
    refine ⟨130884177260150553776388259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174512236346867405035184345 130884177260150553776388259)
    ·
      refine ⟨196326265890225830664582389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130884177260150553776388259 196326265890225830664582389)
      ·
        refine ⟨18405587427208671624804599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 196326265890225830664582389 18405587427208671624804599)
        ·
          refine ⟨27608381140813007437206899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18405587427208671624804599 27608381140813007437206899)
          ·
            refine ⟨41412571711219511155810349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27608381140813007437206899 41412571711219511155810349)
            ·
              refine ⟨15529714391707316683428881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41412571711219511155810349 15529714391707316683428881)
              ·
                refine ⟨11647285793780487512571661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15529714391707316683428881 11647285793780487512571661)
                ·
                  refine ⟨4367732172667682817214373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11647285793780487512571661 4367732172667682817214373)
                  ·
                    refine ⟨818949782375190528227695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4367732172667682817214373 818949782375190528227695)
                    ·
                      rfl

theorem cell23_4784697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 3, 4].length) (baseStart_4784697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784697 prefixEnd_4784697 := by exact prefixLift 4784697
  have htrace : WordTrace (prefixWord ++ tailWord_4784697) baseStart_4784697 baseEnd_4784697 := by
    simpa [prefixWord, tailWord_4784697, baseEnd_4784697] using wordTrace_append hprefix tailTrace_4784697
  have hstable : (prefixWord ++ tailWord_4784697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784697).length < 2 ^ (prefixWord ++ tailWord_4784697).sum := by decide
  have hdescent : baseEnd_4784697 < baseStart_4784697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784714 : List Nat := [3, 1, 2, 1, 1, 4, 1, 5, 1, 4]
def baseStart_4784714 : Nat := 118140960795 + 4784714 * 2 ^ 59
def prefixEnd_4784714 : Nat := 4983230072969 + 3 ^ 40 * 4784714 * 2
def baseEnd_4784714 : Nat := 818952692098899339390169

theorem tailTrace_4784714 : CollatzResearch.WordTrace tailWord_4784714 prefixEnd_4784714 818952692098899339390169 := by
  unfold tailWord_4784714
  simp only [CollatzResearch.WordTrace]
  refine ⟨43628214096951454234638299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116341904258537211292368797 43628214096951454234638299)
  ·
    refine ⟨65442321145427181351957449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43628214096951454234638299 65442321145427181351957449)
    ·
      refine ⟨49081740859070386013968087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65442321145427181351957449 49081740859070386013968087)
      ·
        refine ⟨73622611288605579020952131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49081740859070386013968087 73622611288605579020952131)
        ·
          refine ⟨110433916932908368531428197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73622611288605579020952131 110433916932908368531428197)
          ·
            refine ⟨20706359424920319099642787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110433916932908368531428197 20706359424920319099642787)
            ·
              refine ⟨31059539137380478649464181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20706359424920319099642787 31059539137380478649464181)
              ·
                refine ⟨2911831794129419873387267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31059539137380478649464181 2911831794129419873387267)
                ·
                  refine ⟨4367747691194129810080901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2911831794129419873387267 4367747691194129810080901)
                  ·
                    refine ⟨818952692098899339390169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4367747691194129810080901 818952692098899339390169)
                    ·
                      rfl

theorem cell23_4784714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 5, 1, 4].length) (baseStart_4784714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784714 prefixEnd_4784714 := by exact prefixLift 4784714
  have htrace : WordTrace (prefixWord ++ tailWord_4784714) baseStart_4784714 baseEnd_4784714 := by
    simpa [prefixWord, tailWord_4784714, baseEnd_4784714] using wordTrace_append hprefix tailTrace_4784714
  have hstable : (prefixWord ++ tailWord_4784714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784714).length < 2 ^ (prefixWord ++ tailWord_4784714).sum := by decide
  have hdescent : baseEnd_4784714 < baseStart_4784714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784717 : List Nat := [1, 6, 1, 1, 2, 1, 1, 1, 2, 1, 6]
def baseStart_4784717 : Nat := 118140960795 + 4784717 * 2 ^ 59
def prefixEnd_4784717 : Nat := 4983230072969 + 3 ^ 40 * 4784717 * 2
def baseEnd_4784717 : Nat := 2456859616738661506432993

theorem tailTrace_4784717 : CollatzResearch.WordTrace tailWord_4784717 prefixEnd_4784717 2456859616738661506432993 := by
  unfold tailWord_4784717
  simp only [CollatzResearch.WordTrace]
  refine ⟨174512965806794948450912405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116341977204529965633941603 174512965806794948450912405)
  ·
    refine ⟨8180295272193513208636519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 174512965806794948450912405 8180295272193513208636519)
    ·
      refine ⟨12270442908290269812954779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8180295272193513208636519 12270442908290269812954779)
      ·
        refine ⟨18405664362435404719432169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12270442908290269812954779 18405664362435404719432169)
        ·
          refine ⟨13804248271826553539574127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18405664362435404719432169 13804248271826553539574127)
          ·
            refine ⟨20706372407739830309361191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13804248271826553539574127 20706372407739830309361191)
            ·
              refine ⟨31059558611609745464041787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20706372407739830309361191 31059558611609745464041787)
              ·
                refine ⟨46589337917414618196062681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31059558611609745464041787 46589337917414618196062681)
                ·
                  refine ⟨34942003438060963647047011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46589337917414618196062681 34942003438060963647047011)
                  ·
                    refine ⟨52413005157091445470570517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34942003438060963647047011 52413005157091445470570517)
                    ·
                      refine ⟨2456859616738661506432993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52413005157091445470570517 2456859616738661506432993)
                      ·
                        rfl

theorem cell23_4784717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_4784717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784717 prefixEnd_4784717 := by exact prefixLift 4784717
  have htrace : WordTrace (prefixWord ++ tailWord_4784717) baseStart_4784717 baseEnd_4784717 := by
    simpa [prefixWord, tailWord_4784717, baseEnd_4784717] using wordTrace_append hprefix tailTrace_4784717
  have hstable : (prefixWord ++ tailWord_4784717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784717).length < 2 ^ (prefixWord ++ tailWord_4784717).sum := by decide
  have hdescent : baseEnd_4784717 < baseStart_4784717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784747 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 6, 3, 2]
def baseStart_4784747 : Nat := 118140960795 + 4784747 * 2 ^ 59
def prefixEnd_4784747 : Nat := 4983230072969 + 3 ^ 40 * 4784747 * 2
def baseEnd_4784747 : Nat := 2456875021158296389057855

theorem tailTrace_4784747 : CollatzResearch.WordTrace tailWord_4784747 prefixEnd_4784747 2456875021158296389057855 := by
  unfold tailWord_4784747
  simp only [CollatzResearch.WordTrace]
  refine ⟨174514059996686263574504495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116342706664457509049669663 174514059996686263574504495)
  ·
    refine ⟨261771089995029395361756743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174514059996686263574504495 261771089995029395361756743)
    ·
      refine ⟨392656634992544093042635115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261771089995029395361756743 392656634992544093042635115)
      ·
        refine ⟨588984952488816139563952673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 392656634992544093042635115 588984952488816139563952673)
        ·
          refine ⟨441738714366612104672964505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 588984952488816139563952673 441738714366612104672964505)
          ·
            refine ⟨331304035774959078504723379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 441738714366612104672964505 331304035774959078504723379)
            ·
              refine ⟨496956053662438617757085069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 331304035774959078504723379 496956053662438617757085069)
              ·
                refine ⟨186358520123414481658906901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 496956053662438617757085069 186358520123414481658906901)
                ·
                  refine ⟨8735555630785053827761261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 186358520123414481658906901 8735555630785053827761261)
                  ·
                    refine ⟨3275833361544395185410473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8735555630785053827761261 3275833361544395185410473)
                    ·
                      refine ⟨2456875021158296389057855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3275833361544395185410473 2456875021158296389057855)
                      ·
                        rfl

theorem cell23_4784747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6, 3, 2].length) (baseStart_4784747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784747 prefixEnd_4784747 := by exact prefixLift 4784747
  have htrace : WordTrace (prefixWord ++ tailWord_4784747) baseStart_4784747 baseEnd_4784747 := by
    simpa [prefixWord, tailWord_4784747, baseEnd_4784747] using wordTrace_append hprefix tailTrace_4784747
  have hstable : (prefixWord ++ tailWord_4784747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784747).length < 2 ^ (prefixWord ++ tailWord_4784747).sum := by decide
  have hdescent : baseEnd_4784747 < baseStart_4784747 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784771 : List Nat := [1, 1, 1, 3, 3, 1, 5, 3, 1, 1, 3]
def baseStart_4784771 : Nat := 118140960795 + 4784771 * 2 ^ 59
def prefixEnd_4784771 : Nat := 4983230072969 + 3 ^ 40 * 4784771 * 2
def baseEnd_4784771 : Nat := 2456887344694004295157745

theorem tailTrace_4784771 : CollatzResearch.WordTrace tailWord_4784771 prefixEnd_4784771 2456887344694004295157745 := by
  unfold tailWord_4784771
  simp only [CollatzResearch.WordTrace]
  refine ⟨174514935348599315673378167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116343290232399543782252111 174514935348599315673378167)
  ·
    refine ⟨261772403022898973510067251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174514935348599315673378167 261772403022898973510067251)
    ·
      refine ⟨392658604534348460265100877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261772403022898973510067251 392658604534348460265100877)
      ·
        refine ⟨147246976700380672599412829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 392658604534348460265100877 147246976700380672599412829)
        ·
          refine ⟨55217616262642752224779811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147246976700380672599412829 55217616262642752224779811)
          ·
            refine ⟨82826424393964128337169717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55217616262642752224779811 82826424393964128337169717)
            ·
              refine ⟨7764977286934137031609661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82826424393964128337169717 7764977286934137031609661)
              ·
                refine ⟨2911866482600301386853623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7764977286934137031609661 2911866482600301386853623)
                ·
                  refine ⟨4367799723900452080280435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2911866482600301386853623 4367799723900452080280435)
                  ·
                    refine ⟨6551699585850678120420653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4367799723900452080280435 6551699585850678120420653)
                    ·
                      refine ⟨2456887344694004295157745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6551699585850678120420653 2456887344694004295157745)
                      ·
                        rfl

theorem cell23_4784771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 3, 1, 1, 3].length) (baseStart_4784771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784771 prefixEnd_4784771 := by exact prefixLift 4784771
  have htrace : WordTrace (prefixWord ++ tailWord_4784771) baseStart_4784771 baseEnd_4784771 := by
    simpa [prefixWord, tailWord_4784771, baseEnd_4784771] using wordTrace_append hprefix tailTrace_4784771
  have hstable : (prefixWord ++ tailWord_4784771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784771).length < 2 ^ (prefixWord ++ tailWord_4784771).sum := by decide
  have hdescent : baseEnd_4784771 < baseStart_4784771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784788 : List Nat := [2, 4, 2, 2, 1, 3, 1, 1, 3, 1, 3]
def baseStart_4784788 : Nat := 118140960795 + 4784788 * 2 ^ 59
def prefixEnd_4784788 : Nat := 4983230072969 + 3 ^ 40 * 4784788 * 2
def baseEnd_4784788 : Nat := 2456896073865130728645167

theorem tailTrace_4784788 : CollatzResearch.WordTrace tailWord_4784788 prefixEnd_4784788 2456896073865130728645167 := by
  unfold tailWord_4784788
  simp only [CollatzResearch.WordTrace]
  refine ⟨87257777694768863788373509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116343703593025151717831345 87257777694768863788373509)
  ·
    refine ⟨16360833317769161960320033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87257777694768863788373509 16360833317769161960320033)
    ·
      refine ⟨12270624988326871470240025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16360833317769161960320033 12270624988326871470240025)
      ·
        refine ⟨9202968741245153602680019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12270624988326871470240025 9202968741245153602680019)
        ·
          refine ⟨13804453111867730404020029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9202968741245153602680019 13804453111867730404020029)
          ·
            refine ⟨5176669916950398901507511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13804453111867730404020029 5176669916950398901507511)
            ·
              refine ⟨7765004875425598352261267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5176669916950398901507511 7765004875425598352261267)
              ·
                refine ⟨11647507313138397528391901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7765004875425598352261267 11647507313138397528391901)
                ·
                  refine ⟨4367815242426899073146963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11647507313138397528391901 4367815242426899073146963)
                  ·
                    refine ⟨6551722863640348609720445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4367815242426899073146963 6551722863640348609720445)
                    ·
                      refine ⟨2456896073865130728645167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6551722863640348609720445 2456896073865130728645167)
                      ·
                        rfl

theorem cell23_4784788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_4784788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784788 prefixEnd_4784788 := by exact prefixLift 4784788
  have htrace : WordTrace (prefixWord ++ tailWord_4784788) baseStart_4784788 baseEnd_4784788 := by
    simpa [prefixWord, tailWord_4784788, baseEnd_4784788] using wordTrace_append hprefix tailTrace_4784788
  have hstable : (prefixWord ++ tailWord_4784788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784788).length < 2 ^ (prefixWord ++ tailWord_4784788).sum := by decide
  have hdescent : baseEnd_4784788 < baseStart_4784788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784797 : List Nat := [1, 4, 2, 1, 1, 1, 4, 2, 1, 1, 5]
def baseStart_4784797 : Nat := 118140960795 + 4784797 * 2 ^ 59
def prefixEnd_4784797 : Nat := 4983230072969 + 3 ^ 40 * 4784797 * 2
def baseEnd_4784797 : Nat := 2456900695191021193432625

theorem tailTrace_4784797 : CollatzResearch.WordTrace tailWord_4784797 prefixEnd_4784797 2456900695191021193432625 := by
  unfold tailWord_4784797
  simp only [CollatzResearch.WordTrace]
  refine ⟨174515883646505122113824645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116343922431003414742549763 174515883646505122113824645)
  ·
    refine ⟨32721728183719710396342121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174515883646505122113824645 32721728183719710396342121)
    ·
      refine ⟨24541296137789782797256591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32721728183719710396342121 24541296137789782797256591)
      ·
        refine ⟨36811944206684674195884887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24541296137789782797256591 36811944206684674195884887)
        ·
          refine ⟨55217916310027011293827331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36811944206684674195884887 55217916310027011293827331)
          ·
            refine ⟨82826874465040516940740997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55217916310027011293827331 82826874465040516940740997)
            ·
              refine ⟨15530038962195096926388937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82826874465040516940740997 15530038962195096926388937)
              ·
                refine ⟨11647529221646322694791703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15530038962195096926388937 11647529221646322694791703)
                ·
                  refine ⟨17471293832469484042187555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11647529221646322694791703 17471293832469484042187555)
                  ·
                    refine ⟨26206940748704226063281333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17471293832469484042187555 26206940748704226063281333)
                    ·
                      refine ⟨2456900695191021193432625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26206940748704226063281333 2456900695191021193432625)
                      ·
                        rfl

theorem cell23_4784797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_4784797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784797 prefixEnd_4784797 := by exact prefixLift 4784797
  have htrace : WordTrace (prefixWord ++ tailWord_4784797) baseStart_4784797 baseEnd_4784797 := by
    simpa [prefixWord, tailWord_4784797, baseEnd_4784797] using wordTrace_append hprefix tailTrace_4784797
  have hstable : (prefixWord ++ tailWord_4784797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784797).length < 2 ^ (prefixWord ++ tailWord_4784797).sum := by decide
  have hdescent : baseEnd_4784797 < baseStart_4784797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784804 : List Nat := [2, 3, 1, 2, 2, 1, 3, 3, 2, 4]
def baseStart_4784804 : Nat := 118140960795 + 4784804 * 2 ^ 59
def prefixEnd_4784804 : Nat := 4983230072969 + 3 ^ 40 * 4784804 * 2
def baseEnd_4784804 : Nat := 818968096518534222015031

theorem tailTrace_4784804 : CollatzResearch.WordTrace tailWord_4784804 prefixEnd_4784804 818968096518534222015031 := by
  unfold tailWord_4784804
  simp only [CollatzResearch.WordTrace]
  refine ⟨87258069478739881154664733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116344092638319841539552977 87258069478739881154664733)
  ·
    refine ⟨32721776054527455432999275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87258069478739881154664733 32721776054527455432999275)
    ·
      refine ⟨49082664081791183149498913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32721776054527455432999275 49082664081791183149498913)
      ·
        refine ⟨36811998061343387362124185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49082664081791183149498913 36811998061343387362124185)
        ·
          refine ⟨27608998546007540521593139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36811998061343387362124185 27608998546007540521593139)
          ·
            refine ⟨41413497819011310782389709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27608998546007540521593139 41413497819011310782389709)
            ·
              refine ⟨15530061682129241543396141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41413497819011310782389709 15530061682129241543396141)
              ·
                refine ⟨5823773130798465578773553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15530061682129241543396141 5823773130798465578773553)
                ·
                  refine ⟨4367829848098849184080165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5823773130798465578773553 4367829848098849184080165)
                  ·
                    refine ⟨818968096518534222015031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4367829848098849184080165 818968096518534222015031)
                    ·
                      rfl

theorem cell23_4784804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3, 2, 4].length) (baseStart_4784804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784804 prefixEnd_4784804 := by exact prefixLift 4784804
  have htrace : WordTrace (prefixWord ++ tailWord_4784804) baseStart_4784804 baseEnd_4784804 := by
    simpa [prefixWord, tailWord_4784804, baseEnd_4784804] using wordTrace_append hprefix tailTrace_4784804
  have hstable : (prefixWord ++ tailWord_4784804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784804).length < 2 ^ (prefixWord ++ tailWord_4784804).sum := by decide
  have hdescent : baseEnd_4784804 < baseStart_4784804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784828 : List Nat := [2, 2, 2, 3, 1, 1, 2, 5, 1, 2, 2]
def baseStart_4784828 : Nat := 118140960795 + 4784828 * 2 ^ 59
def prefixEnd_4784828 : Nat := 4983230072969 + 3 ^ 40 * 4784828 * 2
def baseEnd_4784828 : Nat := 2456916613091310572144983

theorem tailTrace_4784828 : CollatzResearch.WordTrace tailWord_4784828 prefixEnd_4784828 2456916613091310572144983 := by
  unfold tailWord_4784828
  simp only [CollatzResearch.WordTrace]
  refine ⟨87258507154696407204101569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116344676206261876272135425 87258507154696407204101569)
  ·
    refine ⟨65443880366022305403076177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87258507154696407204101569 65443880366022305403076177)
    ·
      refine ⟨49082910274516729052307133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65443880366022305403076177 49082910274516729052307133)
      ·
        refine ⟨18406091352943773394615175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49082910274516729052307133 18406091352943773394615175)
        ·
          refine ⟨27609137029415660091922763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18406091352943773394615175 27609137029415660091922763)
          ·
            refine ⟨41413705544123490137884145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27609137029415660091922763 41413705544123490137884145)
            ·
              refine ⟨31060279158092617603413109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41413705544123490137884145 31060279158092617603413109)
              ·
                refine ⟨2911901171071182900319979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31060279158092617603413109 2911901171071182900319979)
                ·
                  refine ⟨4367851756606774350479969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2911901171071182900319979 4367851756606774350479969)
                  ·
                    refine ⟨3275888817455080762859977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4367851756606774350479969 3275888817455080762859977)
                    ·
                      refine ⟨2456916613091310572144983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3275888817455080762859977 2456916613091310572144983)
                      ·
                        rfl

theorem cell23_4784828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_4784828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784828 prefixEnd_4784828 := by exact prefixLift 4784828
  have htrace : WordTrace (prefixWord ++ tailWord_4784828) baseStart_4784828 baseEnd_4784828 := by
    simpa [prefixWord, tailWord_4784828, baseEnd_4784828] using wordTrace_append hprefix tailTrace_4784828
  have hstable : (prefixWord ++ tailWord_4784828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784828).length < 2 ^ (prefixWord ++ tailWord_4784828).sum := by decide
  have hdescent : baseEnd_4784828 < baseStart_4784828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784831 : List Nat := [1, 1, 2, 2, 2, 5, 3, 1, 1, 2, 3]
def baseStart_4784831 : Nat := 118140960795 + 4784831 * 2 ^ 59
def prefixEnd_4784831 : Nat := 4983230072969 + 3 ^ 40 * 4784831 * 2
def baseEnd_4784831 : Nat := 2456918153533274060407469

theorem tailTrace_4784831 : CollatzResearch.WordTrace tailWord_4784831 prefixEnd_4784831 2456918153533274060407469 := by
  unfold tailWord_4784831
  simp only [CollatzResearch.WordTrace]
  refine ⟨174517123728381945920562347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116344749152254630613708231 174517123728381945920562347)
  ·
    refine ⟨261775685592572918880843521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174517123728381945920562347 261775685592572918880843521)
    ·
      refine ⟨196331764194429689160632641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261775685592572918880843521 196331764194429689160632641)
      ·
        refine ⟨147248823145822266870474481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196331764194429689160632641 147248823145822266870474481)
        ·
          refine ⟨110436617359366700152855861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147248823145822266870474481 110436617359366700152855861)
          ·
            refine ⟨10353432877440628139330237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 110436617359366700152855861 10353432877440628139330237)
            ·
              refine ⟨3882537329040235552248839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10353432877440628139330237 3882537329040235552248839)
              ·
                refine ⟨5823805993560353328373259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3882537329040235552248839 5823805993560353328373259)
                ·
                  refine ⟨8735708990340529992559889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5823805993560353328373259 8735708990340529992559889)
                  ·
                    refine ⟨6551781742755397494419917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8735708990340529992559889 6551781742755397494419917)
                    ·
                      refine ⟨2456918153533274060407469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6551781742755397494419917 2456918153533274060407469)
                      ·
                        rfl

theorem cell23_4784831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 1, 1, 2, 3].length) (baseStart_4784831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784831 prefixEnd_4784831 := by exact prefixLift 4784831
  have htrace : WordTrace (prefixWord ++ tailWord_4784831) baseStart_4784831 baseEnd_4784831 := by
    simpa [prefixWord, tailWord_4784831, baseEnd_4784831] using wordTrace_append hprefix tailTrace_4784831
  have hstable : (prefixWord ++ tailWord_4784831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784831).length < 2 ^ (prefixWord ++ tailWord_4784831).sum := by decide
  have hdescent : baseEnd_4784831 < baseStart_4784831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784877 : List Nat := [1, 5, 1, 2, 1, 1, 1, 2, 1, 8]
def baseStart_4784877 : Nat := 118140960795 + 4784877 * 2 ^ 59
def prefixEnd_4784877 : Nat := 4983230072969 + 3 ^ 40 * 4784877 * 2
def baseEnd_4784877 : Nat := 818980591214460293477419

theorem tailTrace_4784877 : CollatzResearch.WordTrace tailWord_4784877 prefixEnd_4784877 818980591214460293477419 := by
  unfold tailWord_4784877
  simp only [CollatzResearch.WordTrace]
  refine ⟨174518801486215295776736885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116345867657476863851157923 174518801486215295776736885)
  ·
    refine ⟨16361137639332683979069083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 174518801486215295776736885 16361137639332683979069083)
    ·
      refine ⟨24541706458999025968603625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16361137639332683979069083 24541706458999025968603625)
      ·
        refine ⟨18406279844249269476452719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24541706458999025968603625 18406279844249269476452719)
        ·
          refine ⟨27609419766373904214679079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18406279844249269476452719 27609419766373904214679079)
          ·
            refine ⟨41414129649560856322018619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27609419766373904214679079 41414129649560856322018619)
            ·
              refine ⟨62121194474341284483027929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41414129649560856322018619 62121194474341284483027929)
              ·
                refine ⟨46590895855755963362270947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62121194474341284483027929 46590895855755963362270947)
                ·
                  refine ⟨69886343783633945043406421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46590895855755963362270947 69886343783633945043406421)
                  ·
                    refine ⟨818980591214460293477419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 69886343783633945043406421 818980591214460293477419)
                    ·
                      rfl

theorem cell23_4784877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_4784877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784877 prefixEnd_4784877 := by exact prefixLift 4784877
  have htrace : WordTrace (prefixWord ++ tailWord_4784877) baseStart_4784877 baseEnd_4784877 := by
    simpa [prefixWord, tailWord_4784877, baseEnd_4784877] using wordTrace_append hprefix tailTrace_4784877
  have hstable : (prefixWord ++ tailWord_4784877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784877).length < 2 ^ (prefixWord ++ tailWord_4784877).sum := by decide
  have hdescent : baseEnd_4784877 < baseStart_4784877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784894 : List Nat := [4, 2, 2, 1, 2, 1, 1, 2, 2, 6]
def baseStart_4784894 : Nat := 118140960795 + 4784894 * 2 ^ 59
def prefixEnd_4784894 : Nat := 4983230072969 + 3 ^ 40 * 4784894 * 2
def baseEnd_4784894 : Nat := 818983500938169104639893

theorem tailTrace_4784894 : CollatzResearch.WordTrace tailWord_4784894 prefixEnd_4784894 818983500938169104639893 := by
  unfold tailWord_4784894
  simp only [CollatzResearch.WordTrace]
  refine ⟨21814927690894213460013217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116346281018102471786737157 21814927690894213460013217)
  ·
    refine ⟨16361195768170660095009913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21814927690894213460013217 16361195768170660095009913)
    ·
      refine ⟨12270896826127995071257435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16361195768170660095009913 12270896826127995071257435)
      ·
        refine ⟨18406345239191992606886153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12270896826127995071257435 18406345239191992606886153)
        ·
          refine ⟨13804758929393994455164615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18406345239191992606886153 13804758929393994455164615)
          ·
            refine ⟨20707138394090991682746923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13804758929393994455164615 20707138394090991682746923)
            ·
              refine ⟨31060707591136487524120385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20707138394090991682746923 31060707591136487524120385)
              ·
                refine ⟨23295530693352365643090289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31060707591136487524120385 23295530693352365643090289)
                ·
                  refine ⟨17471648020014274232317717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23295530693352365643090289 17471648020014274232317717)
                  ·
                    refine ⟨818983500938169104639893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17471648020014274232317717 818983500938169104639893)
                    ·
                      rfl

theorem cell23_4784894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_4784894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784894 prefixEnd_4784894 := by exact prefixLift 4784894
  have htrace : WordTrace (prefixWord ++ tailWord_4784894) baseStart_4784894 baseEnd_4784894 := by
    simpa [prefixWord, tailWord_4784894, baseEnd_4784894] using wordTrace_append hprefix tailTrace_4784894
  have hstable : (prefixWord ++ tailWord_4784894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784894).length < 2 ^ (prefixWord ++ tailWord_4784894).sum := by decide
  have hdescent : baseEnd_4784894 < baseStart_4784894 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784958 : List Nat := [4, 2, 1, 2, 4, 1, 1, 1, 7]
def baseStart_4784958 : Nat := 118140960795 + 4784958 * 2 ^ 59
def prefixEnd_4784958 : Nat := 4983230072969 + 3 ^ 40 * 4784958 * 2
def baseEnd_4784958 : Nat := 272998151730710562613265

theorem tailTrace_4784958 : CollatzResearch.WordTrace tailWord_4784958 prefixEnd_4784958 272998151730710562613265 := by
  unfold tailWord_4784958
  simp only [CollatzResearch.WordTrace]
  refine ⟨21815219474865230826304441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116347837199281231073623685 21815219474865230826304441)
  ·
    refine ⟨16361414606148923119728331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21815219474865230826304441 16361414606148923119728331)
    ·
      refine ⟨24542121909223384679592497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16361414606148923119728331 24542121909223384679592497)
      ·
        refine ⟨18406591431917538509694373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24542121909223384679592497 18406591431917538509694373)
        ·
          refine ⟨3451235893484538470567695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18406591431917538509694373 3451235893484538470567695)
          ·
            refine ⟨5176853840226807705851543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3451235893484538470567695 5176853840226807705851543)
            ·
              refine ⟨7765280760340211558777315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5176853840226807705851543 7765280760340211558777315)
              ·
                refine ⟨11647921140510317338165973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7765280760340211558777315 11647921140510317338165973)
                ·
                  refine ⟨272998151730710562613265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11647921140510317338165973 272998151730710562613265)
                  ·
                    rfl

theorem cell23_4784958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_4784958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784958 prefixEnd_4784958 := by exact prefixLift 4784958
  have htrace : WordTrace (prefixWord ++ tailWord_4784958) baseStart_4784958 baseEnd_4784958 := by
    simpa [prefixWord, tailWord_4784958, baseEnd_4784958] using wordTrace_append hprefix tailTrace_4784958
  have hstable : (prefixWord ++ tailWord_4784958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784958).length < 2 ^ (prefixWord ++ tailWord_4784958).sum := by decide
  have hdescent : baseEnd_4784958 < baseStart_4784958 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784984 : List Nat := [2, 1, 2, 2, 1, 1, 1, 6, 3, 4]
def baseStart_4784984 : Nat := 118140960795 + 4784984 * 2 ^ 59
def prefixEnd_4784984 : Nat := 4983230072969 + 3 ^ 40 * 4784984 * 2
def baseEnd_4784984 : Nat := 818998905357803987264755

theorem tailTrace_4784984 : CollatzResearch.WordTrace tailWord_4784984 prefixEnd_4784984 818998905357803987264755 := by
  unfold tailWord_4784984
  simp only [CollatzResearch.WordTrace]
  refine ⟨87261352048413826525441003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116348469397885102033921337 87261352048413826525441003)
  ·
    refine ⟨130892028072620739788161505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87261352048413826525441003 130892028072620739788161505)
    ·
      refine ⟨98169021054465554841121129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130892028072620739788161505 98169021054465554841121129)
      ·
        refine ⟨73626765790849166130840847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98169021054465554841121129 73626765790849166130840847)
        ·
          refine ⟨110440148686273749196261271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73626765790849166130840847 110440148686273749196261271)
          ·
            refine ⟨165660223029410623794391907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110440148686273749196261271 165660223029410623794391907)
            ·
              refine ⟨248490334544115935691587861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165660223029410623794391907 248490334544115935691587861)
              ·
                refine ⟨11647984431755434485543181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 248490334544115935691587861 11647984431755434485543181)
                ·
                  refine ⟨4367994161908287932078693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11647984431755434485543181 4367994161908287932078693)
                  ·
                    refine ⟨818998905357803987264755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4367994161908287932078693 818998905357803987264755)
                    ·
                      rfl

theorem cell23_4784984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 3, 4].length) (baseStart_4784984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784984 prefixEnd_4784984 := by exact prefixLift 4784984
  have htrace : WordTrace (prefixWord ++ tailWord_4784984) baseStart_4784984 baseEnd_4784984 := by
    simpa [prefixWord, tailWord_4784984, baseEnd_4784984] using wordTrace_append hprefix tailTrace_4784984
  have hstable : (prefixWord ++ tailWord_4784984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784984).length < 2 ^ (prefixWord ++ tailWord_4784984).sum := by decide
  have hdescent : baseEnd_4784984 < baseStart_4784984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4784997 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 10]
def baseStart_4784997 : Nat := 118140960795 + 4784997 * 2 ^ 59
def prefixEnd_4784997 : Nat := 4983230072969 + 3 ^ 40 * 4784997 * 2
def baseEnd_4784997 : Nat := 273000376813546712325745

theorem tailTrace_4784997 : CollatzResearch.WordTrace tailWord_4784997 prefixEnd_4784997 273000376813546712325745 := by
  unfold tailWord_4784997
  simp only [CollatzResearch.WordTrace]
  refine ⟨174523178245780556271105245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116348785497187037514070163 174523178245780556271105245)
  ·
    refine ⟨65446191842167708601664467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174523178245780556271105245 65446191842167708601664467)
    ·
      refine ⟨98169287763251562902496701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65446191842167708601664467 98169287763251562902496701)
      ·
        refine ⟨36813482911219336088436263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98169287763251562902496701 36813482911219336088436263)
        ·
          refine ⟨55220224366829004132654395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36813482911219336088436263 55220224366829004132654395)
          ·
            refine ⟨82830336550243506198981593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55220224366829004132654395 82830336550243506198981593)
            ·
              refine ⟨62122752412682629649236195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82830336550243506198981593 62122752412682629649236195)
              ·
                refine ⟨93184128619023944473854293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62122752412682629649236195 93184128619023944473854293)
                ·
                  refine ⟨273000376813546712325745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 93184128619023944473854293 273000376813546712325745)
                  ·
                    rfl

theorem cell23_4784997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 10].length) (baseStart_4784997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4784997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4784997 prefixEnd_4784997 := by exact prefixLift 4784997
  have htrace : WordTrace (prefixWord ++ tailWord_4784997) baseStart_4784997 baseEnd_4784997 := by
    simpa [prefixWord, tailWord_4784997, baseEnd_4784997] using wordTrace_append hprefix tailTrace_4784997
  have hstable : (prefixWord ++ tailWord_4784997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4784997).length < 2 ^ (prefixWord ++ tailWord_4784997).sum := by decide
  have hdescent : baseEnd_4784997 < baseStart_4784997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4784997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4785109 : List Nat := [1, 3, 2, 3, 4, 1, 1, 3, 1, 1, 3]
def baseStart_4785109 : Nat := 118140960795 + 4785109 * 2 ^ 59
def prefixEnd_4785109 : Nat := 4983230072969 + 3 ^ 40 * 4785109 * 2
def baseEnd_4785109 : Nat := 2457060901155223972731191

theorem tailTrace_4785109 : CollatzResearch.WordTrace tailWord_4785109 prefixEnd_4785109 2457060901155223972731191 := by
  unfold tailWord_4785109
  simp only [CollatzResearch.WordTrace]
  refine ⟨174527263221374799399182381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116351508814249866266121587 174527263221374799399182381)
  ·
    refine ⟨65447723708015549774693393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174527263221374799399182381 65447723708015549774693393)
    ·
      refine ⟨49085792781011662331020045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65447723708015549774693393 49085792781011662331020045)
      ·
        refine ⟨18407172292879373374132517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49085792781011662331020045 18407172292879373374132517)
        ·
          refine ⟨3451344804914882507649847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18407172292879373374132517 3451344804914882507649847)
          ·
            refine ⟨5177017207372323761474771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3451344804914882507649847 5177017207372323761474771)
            ·
              refine ⟨7765525811058485642212157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5177017207372323761474771 7765525811058485642212157)
              ·
                refine ⟨2912072179146932115829559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7765525811058485642212157 2912072179146932115829559)
                ·
                  refine ⟨4368108268720398173744339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2912072179146932115829559 4368108268720398173744339)
                  ·
                    refine ⟨6552162403080597260616509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4368108268720398173744339 6552162403080597260616509)
                    ·
                      refine ⟨2457060901155223972731191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6552162403080597260616509 2457060901155223972731191)
                      ·
                        rfl

theorem cell23_4785109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_4785109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4785109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4785109 prefixEnd_4785109 := by exact prefixLift 4785109
  have htrace : WordTrace (prefixWord ++ tailWord_4785109) baseStart_4785109 baseEnd_4785109 := by
    simpa [prefixWord, tailWord_4785109, baseEnd_4785109] using wordTrace_append hprefix tailTrace_4785109
  have hstable : (prefixWord ++ tailWord_4785109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4785109).length < 2 ^ (prefixWord ++ tailWord_4785109).sum := by decide
  have hdescent : baseEnd_4785109 < baseStart_4785109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4785109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4785138 : List Nat := [3, 2, 1, 5, 1, 1, 2, 8]
def baseStart_4785138 : Nat := 118140960795 + 4785138 * 2 ^ 59
def prefixEnd_4785138 : Nat := 4983230072969 + 3 ^ 40 * 4785138 * 2
def baseEnd_4785138 : Nat := 91002807114600161454391

theorem tailTrace_4785138 : CollatzResearch.WordTrace tailWord_4785138 prefixEnd_4785138 91002807114600161454391 := by
  unfold tailWord_4785138
  simp only [CollatzResearch.WordTrace]
  refine ⟨43632080234567434337997017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116352213958846491567992045 43632080234567434337997017)
  ·
    refine ⟨32724060175925575753497763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43632080234567434337997017 32724060175925575753497763)
    ·
      refine ⟨49086090263888363630246645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32724060175925575753497763 49086090263888363630246645)
      ·
        refine ⟨4601820962239534090335623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49086090263888363630246645 4601820962239534090335623)
        ·
          refine ⟨6902731443359301135503435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4601820962239534090335623 6902731443359301135503435)
          ·
            refine ⟨10354097165038951703255153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6902731443359301135503435 10354097165038951703255153)
            ·
              refine ⟨7765572873779213777441365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10354097165038951703255153 7765572873779213777441365)
              ·
                refine ⟨91002807114600161454391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7765572873779213777441365 91002807114600161454391)
                ·
                  rfl

theorem cell23_4785138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 8].length) (baseStart_4785138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4785138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4785138 prefixEnd_4785138 := by exact prefixLift 4785138
  have htrace : WordTrace (prefixWord ++ tailWord_4785138) baseStart_4785138 baseEnd_4785138 := by
    simpa [prefixWord, tailWord_4785138, baseEnd_4785138] using wordTrace_append hprefix tailTrace_4785138
  have hstable : (prefixWord ++ tailWord_4785138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4785138).length < 2 ^ (prefixWord ++ tailWord_4785138).sum := by decide
  have hdescent : baseEnd_4785138 < baseStart_4785138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4785138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4785142 : List Nat := [5, 1, 1, 1, 3, 3, 2, 1, 2, 4]
def baseStart_4785142 : Nat := 118140960795 + 4785142 * 2 ^ 59
def prefixEnd_4785142 : Nat := 4983230072969 + 3 ^ 40 * 4785142 * 2
def baseEnd_4785142 : Nat := 819025948672274114539513

theorem tailTrace_4785142 : CollatzResearch.WordTrace tailWord_4785142 prefixEnd_4785142 819025948672274114539513 := by
  unfold tailWord_4785142
  simp only [CollatzResearch.WordTrace]
  refine ⟨10908029176890952877195855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116352311220170164023422453 10908029176890952877195855)
  ·
    refine ⟨16362043765336429315793783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10908029176890952877195855 16362043765336429315793783)
    ·
      refine ⟨24543065648004643973690675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16362043765336429315793783 24543065648004643973690675)
      ·
        refine ⟨36814598472006965960536013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24543065648004643973690675 36814598472006965960536013)
        ·
          refine ⟨13805474427002612235201005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36814598472006965960536013 13805474427002612235201005)
          ·
            refine ⟨5177052910125979588200377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13805474427002612235201005 5177052910125979588200377)
            ·
              refine ⟨3882789682594484691150283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5177052910125979588200377 3882789682594484691150283)
              ·
                refine ⟨5824184523891727036725425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3882789682594484691150283 5824184523891727036725425)
                ·
                  refine ⟨4368138392918795277544069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5824184523891727036725425 4368138392918795277544069)
                  ·
                    refine ⟨819025948672274114539513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4368138392918795277544069 819025948672274114539513)
                    ·
                      rfl

theorem cell23_4785142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_4785142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4785142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4785142 prefixEnd_4785142 := by exact prefixLift 4785142
  have htrace : WordTrace (prefixWord ++ tailWord_4785142) baseStart_4785142 baseEnd_4785142 := by
    simpa [prefixWord, tailWord_4785142, baseEnd_4785142] using wordTrace_append hprefix tailTrace_4785142
  have hstable : (prefixWord ++ tailWord_4785142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4785142).length < 2 ^ (prefixWord ++ tailWord_4785142).sum := by decide
  have hdescent : baseEnd_4785142 < baseStart_4785142 := by decide
  rcases family_descends (prefixWord ++ tailWord_4785142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4785201 : List Nat := [1, 2, 2, 3, 1, 2, 3, 1, 2, 2, 4]
def baseStart_4785201 : Nat := 118140960795 + 4785201 * 2 ^ 59
def prefixEnd_4785201 : Nat := 4983230072969 + 3 ^ 40 * 4785201 * 2
def baseEnd_4785201 : Nat := 2457108141375437612780767

theorem tailTrace_4785201 : CollatzResearch.WordTrace tailWord_4785201 prefixEnd_4785201 2457108141375437612780767 := by
  unfold tailWord_4785201
  simp only [CollatzResearch.WordTrace]
  refine ⟨174530618737041499111531457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116353745824694332741020971 174530618737041499111531457)
  ·
    refine ⟨130897964052781124333648593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174530618737041499111531457 130897964052781124333648593)
    ·
      refine ⟨98173473039585843250236445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130897964052781124333648593 98173473039585843250236445)
      ·
        refine ⟨36815052389844691218838667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98173473039585843250236445 36815052389844691218838667)
        ·
          refine ⟨55222578584767036828258001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36815052389844691218838667 55222578584767036828258001)
          ·
            refine ⟨41416933938575277621193501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55222578584767036828258001 41416933938575277621193501)
            ·
              refine ⟨15531350226965729107947563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41416933938575277621193501 15531350226965729107947563)
              ·
                refine ⟨23297025340448593661921345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15531350226965729107947563 23297025340448593661921345)
                ·
                  refine ⟨17472769005336445246441009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23297025340448593661921345 17472769005336445246441009)
                  ·
                    refine ⟨13104576754002333934830757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17472769005336445246441009 13104576754002333934830757)
                    ·
                      refine ⟨2457108141375437612780767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13104576754002333934830757 2457108141375437612780767)
                      ·
                        rfl

theorem cell23_4785201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_4785201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4785201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4785201 prefixEnd_4785201 := by exact prefixLift 4785201
  have htrace : WordTrace (prefixWord ++ tailWord_4785201) baseStart_4785201 baseEnd_4785201 := by
    simpa [prefixWord, tailWord_4785201, baseEnd_4785201] using wordTrace_append hprefix tailTrace_4785201
  have hstable : (prefixWord ++ tailWord_4785201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4785201).length < 2 ^ (prefixWord ++ tailWord_4785201).sum := by decide
  have hdescent : baseEnd_4785201 < baseStart_4785201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4785201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4785222 : List Nat := [6, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2]
def baseStart_4785222 : Nat := 118140960795 + 4785222 * 2 ^ 59
def prefixEnd_4785222 : Nat := 4983230072969 + 3 ^ 40 * 4785222 * 2
def baseEnd_4785222 : Nat := 2457118924469182030618171

theorem tailTrace_4785222 : CollatzResearch.WordTrace tailWord_4785222 prefixEnd_4785222 2457118924469182030618171 := by
  unfold tailWord_4785222
  simp only [CollatzResearch.WordTrace]
  refine ⟨5454105770936419365563935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 116354256446643613132030613 5454105770936419365563935)
  ·
    refine ⟨8181158656404629048345903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5454105770936419365563935 8181158656404629048345903)
    ·
      refine ⟨12271737984606943572518855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8181158656404629048345903 12271737984606943572518855)
      ·
        refine ⟨18407606976910415358778283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12271737984606943572518855 18407606976910415358778283)
        ·
          refine ⟨27611410465365623038167425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18407606976910415358778283 27611410465365623038167425)
          ·
            refine ⟨20708557849024217278625569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27611410465365623038167425 20708557849024217278625569)
            ·
              refine ⟨15531418386768162958969177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20708557849024217278625569 15531418386768162958969177)
              ·
                refine ⟨11648563790076122219226883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15531418386768162958969177 11648563790076122219226883)
                ·
                  refine ⟨17472845685114183328840325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11648563790076122219226883 17472845685114183328840325)
                  ·
                    refine ⟨3276158565958909374157561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17472845685114183328840325 3276158565958909374157561)
                    ·
                      refine ⟨2457118924469182030618171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3276158565958909374157561 2457118924469182030618171)
                      ·
                        rfl

theorem cell23_4785222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_4785222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4785222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4785222 prefixEnd_4785222 := by exact prefixLift 4785222
  have htrace : WordTrace (prefixWord ++ tailWord_4785222) baseStart_4785222 baseEnd_4785222 := by
    simpa [prefixWord, tailWord_4785222, baseEnd_4785222] using wordTrace_append hprefix tailTrace_4785222
  have hstable : (prefixWord ++ tailWord_4785222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4785222).length < 2 ^ (prefixWord ++ tailWord_4785222).sum := by decide
  have hdescent : baseEnd_4785222 < baseStart_4785222 := by decide
  rcases family_descends (prefixWord ++ tailWord_4785222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4785245 : List Nat := [1, 4, 4, 1, 2, 1, 2, 1, 7]
def baseStart_4785245 : Nat := 118140960795 + 4785245 * 2 ^ 59
def prefixEnd_4785245 : Nat := 4983230072969 + 3 ^ 40 * 4785245 * 2
def baseEnd_4785245 : Nat := 273014526058248382292285

theorem tailTrace_4785245 : CollatzResearch.WordTrace tailWord_4785245 prefixEnd_4785245 273014526058248382292285 := by
  unfold tailWord_4785245
  simp only [CollatzResearch.WordTrace]
  refine ⟨174532223548882094626133189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116354815699254729750755459 174532223548882094626133189)
  ·
    refine ⟨32724791915415392742399973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174532223548882094626133189 32724791915415392742399973)
    ·
      refine ⟨6135898484140386139199995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32724791915415392742399973 6135898484140386139199995)
      ·
        refine ⟨9203847726210579208799993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6135898484140386139199995 9203847726210579208799993)
        ·
          refine ⟨6902885794657934406599995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9203847726210579208799993 6902885794657934406599995)
          ·
            refine ⟨10354328691986901609899993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6902885794657934406599995 10354328691986901609899993)
            ·
              refine ⟨7765746518990176207424995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10354328691986901609899993 7765746518990176207424995)
              ·
                refine ⟨11648619778485264311137493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7765746518990176207424995 11648619778485264311137493)
                ·
                  refine ⟨273014526058248382292285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11648619778485264311137493 273014526058248382292285)
                  ·
                    rfl

theorem cell23_4785245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 7].length) (baseStart_4785245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4785245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4785245 prefixEnd_4785245 := by exact prefixLift 4785245
  have htrace : WordTrace (prefixWord ++ tailWord_4785245) baseStart_4785245 baseEnd_4785245 := by
    simpa [prefixWord, tailWord_4785245, baseEnd_4785245] using wordTrace_append hprefix tailTrace_4785245
  have hstable : (prefixWord ++ tailWord_4785245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4785245).length < 2 ^ (prefixWord ++ tailWord_4785245).sum := by decide
  have hdescent : baseEnd_4785245 < baseStart_4785245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4785245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4785256 : List Nat := [2, 1, 4, 4, 1, 1, 3, 1, 2, 2, 2]
def baseStart_4785256 : Nat := 118140960795 + 4785256 * 2 ^ 59
def prefixEnd_4785256 : Nat := 4983230072969 + 3 ^ 40 * 4785256 * 2
def baseEnd_4785256 : Nat := 2457136382811434897593015

theorem tailTrace_4785256 : CollatzResearch.WordTrace tailWord_4785256 prefixEnd_4785256 2457136382811434897593015 := by
  unfold tailWord_4785256
  simp only [CollatzResearch.WordTrace]
  refine ⟨87266312375921121752391811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116355083167894829003189081 87266312375921121752391811)
  ·
    refine ⟨130899468563881682628587717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87266312375921121752391811 130899468563881682628587717)
    ·
      refine ⟨24543650355727815492860197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130899468563881682628587717 24543650355727815492860197)
      ·
        refine ⟨4601934441698965404911287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24543650355727815492860197 4601934441698965404911287)
        ·
          refine ⟨6902901662548448107366931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4601934441698965404911287 6902901662548448107366931)
          ·
            refine ⟨10354352493822672161050397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6902901662548448107366931 10354352493822672161050397)
            ·
              refine ⟨3882882185183502060393899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10354352493822672161050397 3882882185183502060393899)
              ·
                refine ⟨5824323277775253090590849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3882882185183502060393899 5824323277775253090590849)
                ·
                  refine ⟨4368242458331439817943137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5824323277775253090590849 4368242458331439817943137)
                  ·
                    refine ⟨3276181843748579863457353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4368242458331439817943137 3276181843748579863457353)
                    ·
                      refine ⟨2457136382811434897593015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3276181843748579863457353 2457136382811434897593015)
                      ·
                        rfl

theorem cell23_4785256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_4785256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4785256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4785256 prefixEnd_4785256 := by exact prefixLift 4785256
  have htrace : WordTrace (prefixWord ++ tailWord_4785256) baseStart_4785256 baseEnd_4785256 := by
    simpa [prefixWord, tailWord_4785256, baseEnd_4785256] using wordTrace_append hprefix tailTrace_4785256
  have hstable : (prefixWord ++ tailWord_4785256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4785256).length < 2 ^ (prefixWord ++ tailWord_4785256).sum := by decide
  have hdescent : baseEnd_4785256 < baseStart_4785256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4785256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4785361 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 5, 6]
def baseStart_4785361 : Nat := 118140960795 + 4785361 * 2 ^ 59
def prefixEnd_4785361 : Nat := 4983230072969 + 3 ^ 40 * 4785361 * 2
def baseEnd_4785361 : Nat := 819063432760052328926677

theorem tailTrace_4785361 : CollatzResearch.WordTrace tailWord_4785361 prefixEnd_4785361 819063432760052328926677 := by
  unfold tailWord_4785361
  simp only [CollatzResearch.WordTrace]
  refine ⟨174536454416461846437355937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116357636277641230958237291 174536454416461846437355937)
  ·
    refine ⟨130902340812346384828016953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174536454416461846437355937 130902340812346384828016953)
    ·
      refine ⟨98176755609259788621012715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130902340812346384828016953 98176755609259788621012715)
      ·
        refine ⟨147265133413889682931519073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98176755609259788621012715 147265133413889682931519073)
        ·
          refine ⟨110448850060417262198639305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147265133413889682931519073 110448850060417262198639305)
          ·
            refine ⟨82836637545312946648979479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110448850060417262198639305 82836637545312946648979479)
            ·
              refine ⟨124254956317969419973469219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82836637545312946648979479 124254956317969419973469219)
              ·
                refine ⟨186382434476954129960203829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124254956317969419973469219 186382434476954129960203829)
                ·
                  refine ⟨17473353232214449683769109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 186382434476954129960203829 17473353232214449683769109)
                  ·
                    refine ⟨819063432760052328926677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17473353232214449683769109 819063432760052328926677)
                    ·
                      rfl

theorem cell23_4785361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 6].length) (baseStart_4785361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4785361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4785361 prefixEnd_4785361 := by exact prefixLift 4785361
  have htrace : WordTrace (prefixWord ++ tailWord_4785361) baseStart_4785361 baseEnd_4785361 := by
    simpa [prefixWord, tailWord_4785361, baseEnd_4785361] using wordTrace_append hprefix tailTrace_4785361
  have hstable : (prefixWord ++ tailWord_4785361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4785361).length < 2 ^ (prefixWord ++ tailWord_4785361).sum := by decide
  have hdescent : baseEnd_4785361 < baseStart_4785361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4785361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4785389 : List Nat := [1, 5, 1, 2, 2, 3, 1, 1, 2, 3, 2]
def baseStart_4785389 : Nat := 118140960795 + 4785389 * 2 ^ 59
def prefixEnd_4785389 : Nat := 4983230072969 + 3 ^ 40 * 4785389 * 2
def baseEnd_4785389 : Nat := 2457204675738482877229903

theorem tailTrace_4785389 : CollatzResearch.WordTrace tailWord_4785389 prefixEnd_4785389 2457204675738482877229903 := by
  unfold tailWord_4785389
  simp only [CollatzResearch.WordTrace]
  refine ⟨174537475660360407219375221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116358317106906938146250147 174537475660360407219375221)
  ·
    refine ⟨16362888343158788176816427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 174537475660360407219375221 16362888343158788176816427)
    ·
      refine ⟨24544332514738182265224641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16362888343158788176816427 24544332514738182265224641)
      ·
        refine ⟨18408249386053636698918481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24544332514738182265224641 18408249386053636698918481)
        ·
          refine ⟨13806187039540227524188861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18408249386053636698918481 13806187039540227524188861)
          ·
            refine ⟨5177320139827585321570823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13806187039540227524188861 5177320139827585321570823)
            ·
              refine ⟨7765980209741377982356235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5177320139827585321570823 7765980209741377982356235)
              ·
                refine ⟨11648970314612066973534353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7765980209741377982356235 11648970314612066973534353)
                ·
                  refine ⟨8736727735959050230150765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11648970314612066973534353 8736727735959050230150765)
                  ·
                    refine ⟨3276272900984643836306537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8736727735959050230150765 3276272900984643836306537)
                    ·
                      refine ⟨2457204675738482877229903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3276272900984643836306537 2457204675738482877229903)
                      ·
                        rfl

theorem cell23_4785389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_4785389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4785389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4785389 prefixEnd_4785389 := by exact prefixLift 4785389
  have htrace : WordTrace (prefixWord ++ tailWord_4785389) baseStart_4785389 baseEnd_4785389 := by
    simpa [prefixWord, tailWord_4785389, baseEnd_4785389] using wordTrace_append hprefix tailTrace_4785389
  have hstable : (prefixWord ++ tailWord_4785389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4785389).length < 2 ^ (prefixWord ++ tailWord_4785389).sum := by decide
  have hdescent : baseEnd_4785389 < baseStart_4785389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4785389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4785398 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6]
def baseStart_4785398 : Nat := 118140960795 + 4785398 * 2 ^ 59
def prefixEnd_4785398 : Nat := 4983230072969 + 3 ^ 40 * 4785398 * 2
def baseEnd_4785398 : Nat := 2457209297064373342017361

theorem tailTrace_4785398 : CollatzResearch.WordTrace tailWord_4785398 prefixEnd_4785398 2457209297064373342017361 := by
  unfold tailWord_4785398
  simp only [CollatzResearch.WordTrace]
  refine ⟨10908612744832987609778303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116358535944885201170968565 10908612744832987609778303)
  ·
    refine ⟨16362919117249481414667455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10908612744832987609778303 16362919117249481414667455)
    ·
      refine ⟨24544378675874222122001183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16362919117249481414667455 24544378675874222122001183)
      ·
        refine ⟨36816568013811333183001775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24544378675874222122001183 36816568013811333183001775)
        ·
          refine ⟨55224852020716999774502663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36816568013811333183001775 55224852020716999774502663)
          ·
            refine ⟨82837278031075499661753995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55224852020716999774502663 82837278031075499661753995)
            ·
              refine ⟨124255917046613249492630993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82837278031075499661753995 124255917046613249492630993)
              ·
                refine ⟨93191937784959937119473245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124255917046613249492630993 93191937784959937119473245)
                ·
                  refine ⟨34946976669359976419802467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93191937784959937119473245 34946976669359976419802467)
                  ·
                    refine ⟨52420465004039964629703701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34946976669359976419802467 52420465004039964629703701)
                    ·
                      refine ⟨2457209297064373342017361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52420465004039964629703701 2457209297064373342017361)
                      ·
                        rfl

theorem cell23_4785398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_4785398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4785398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4785398 prefixEnd_4785398 := by exact prefixLift 4785398
  have htrace : WordTrace (prefixWord ++ tailWord_4785398) baseStart_4785398 baseEnd_4785398 := by
    simpa [prefixWord, tailWord_4785398, baseEnd_4785398] using wordTrace_append hprefix tailTrace_4785398
  have hstable : (prefixWord ++ tailWord_4785398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4785398).length < 2 ^ (prefixWord ++ tailWord_4785398).sum := by decide
  have hdescent : baseEnd_4785398 < baseStart_4785398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4785398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4785412 : List Nat := [2, 3, 2, 2, 2, 1, 3, 2, 2, 4]
def baseStart_4785412 : Nat := 118140960795 + 4785412 * 2 ^ 59
def prefixEnd_4785412 : Nat := 4983230072969 + 3 ^ 40 * 4785412 * 2
def baseEnd_4785412 : Nat := 819072161931178762414099

theorem tailTrace_4785412 : CollatzResearch.WordTrace tailWord_4785412 prefixEnd_4785412 819072161931178762414099 := by
  unfold tailWord_4785412
  simp only [CollatzResearch.WordTrace]
  refine ⟨87269157269638541073731245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116358876359518054764974993 87269157269638541073731245)
  ·
    refine ⟨32725933976114452902649217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87269157269638541073731245 32725933976114452902649217)
    ·
      refine ⟨24544450482085839676986913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32725933976114452902649217 24544450482085839676986913)
      ·
        refine ⟨18408337861564379757740185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24544450482085839676986913 18408337861564379757740185)
        ·
          refine ⟨13806253396173284818305139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18408337861564379757740185 13806253396173284818305139)
          ·
            refine ⟨20709380094259927227457709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13806253396173284818305139 20709380094259927227457709)
            ·
              refine ⟨7766017535347472710296641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20709380094259927227457709 7766017535347472710296641)
              ·
                refine ⟨5824513151510604532722481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7766017535347472710296641 5824513151510604532722481)
                ·
                  refine ⟨4368384863632953399541861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5824513151510604532722481 4368384863632953399541861)
                  ·
                    refine ⟨819072161931178762414099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4368384863632953399541861 819072161931178762414099)
                    ·
                      rfl

theorem cell23_4785412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_4785412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4785412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4785412 prefixEnd_4785412 := by exact prefixLift 4785412
  have htrace : WordTrace (prefixWord ++ tailWord_4785412) baseStart_4785412 baseEnd_4785412 := by
    simpa [prefixWord, tailWord_4785412, baseEnd_4785412] using wordTrace_append hprefix tailTrace_4785412
  have hstable : (prefixWord ++ tailWord_4785412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4785412).length < 2 ^ (prefixWord ++ tailWord_4785412).sum := by decide
  have hdescent : baseEnd_4785412 < baseStart_4785412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4785412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4785419 : List Nat := [1, 1, 1, 1, 5, 3, 2, 4, 1, 2, 2]
def baseStart_4785419 : Nat := 118140960795 + 4785419 * 2 ^ 59
def prefixEnd_4785419 : Nat := 4983230072969 + 3 ^ 40 * 4785419 * 2
def baseEnd_4785419 : Nat := 2457220080158117759854765

theorem tailTrace_4785419 : CollatzResearch.WordTrace tailWord_4785419 prefixEnd_4785419 2457220080158117759854765 := by
  unfold tailWord_4785419
  simp only [CollatzResearch.WordTrace]
  refine ⟨174538569850251722342967311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116359046566834481561978207 174538569850251722342967311)
  ·
    refine ⟨261807854775377583514450967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174538569850251722342967311 261807854775377583514450967)
    ·
      refine ⟨392711782163066375271676451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261807854775377583514450967 392711782163066375271676451)
      ·
        refine ⟨589067673244599562907514677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 392711782163066375271676451 589067673244599562907514677)
        ·
          refine ⟨55225094366681209022579501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 589067673244599562907514677 55225094366681209022579501)
          ·
            refine ⟨20709410387505453383467313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55225094366681209022579501 20709410387505453383467313)
            ·
              refine ⟨15532057790629090037600485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20709410387505453383467313 15532057790629090037600485)
              ·
                refine ⟨2912260835742954382050091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15532057790629090037600485 2912260835742954382050091)
                ·
                  refine ⟨4368391253614431573075137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2912260835742954382050091 4368391253614431573075137)
                  ·
                    refine ⟨3276293440210823679806353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4368391253614431573075137 3276293440210823679806353)
                    ·
                      refine ⟨2457220080158117759854765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3276293440210823679806353 2457220080158117759854765)
                      ·
                        rfl

theorem cell23_4785419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 4, 1, 2, 2].length) (baseStart_4785419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4785419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4785419 prefixEnd_4785419 := by exact prefixLift 4785419
  have htrace : WordTrace (prefixWord ++ tailWord_4785419) baseStart_4785419 baseEnd_4785419 := by
    simpa [prefixWord, tailWord_4785419, baseEnd_4785419] using wordTrace_append hprefix tailTrace_4785419
  have hstable : (prefixWord ++ tailWord_4785419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4785419).length < 2 ^ (prefixWord ++ tailWord_4785419).sum := by decide
  have hdescent : baseEnd_4785419 < baseStart_4785419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4785419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4785442 : List Nat := [3, 3, 1, 1, 4, 2, 2, 7]
def baseStart_4785442 : Nat := 118140960795 + 4785442 * 2 ^ 59
def prefixEnd_4785442 : Nat := 4983230072969 + 3 ^ 40 * 4785442 * 2
def baseEnd_4785442 : Nat := 91008588526413747032117

theorem tailTrace_4785442 : CollatzResearch.WordTrace tailWord_4785442 prefixEnd_4785442 91008588526413747032117 := by
  unfold tailWord_4785442
  simp only [CollatzResearch.WordTrace]
  refine ⟨43634852182292099317763645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116359605819445598180703053 43634852182292099317763645)
  ·
    refine ⟨16363069568359537244161367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43634852182292099317763645 16363069568359537244161367)
    ·
      refine ⟨24544604352539305866242051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16363069568359537244161367 24544604352539305866242051)
      ·
        refine ⟨36816906528808958799363077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24544604352539305866242051 36816906528808958799363077)
        ·
          refine ⟨6903169974151679774880577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36816906528808958799363077 6903169974151679774880577)
          ·
            refine ⟨5177377480613759831160433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6903169974151679774880577 5177377480613759831160433)
            ·
              refine ⟨3883033110460319873370325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5177377480613759831160433 3883033110460319873370325)
              ·
                refine ⟨91008588526413747032117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3883033110460319873370325 91008588526413747032117)
                ·
                  rfl

theorem cell23_4785442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 7].length) (baseStart_4785442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4785442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4785442 prefixEnd_4785442 := by exact prefixLift 4785442
  have htrace : WordTrace (prefixWord ++ tailWord_4785442) baseStart_4785442 baseEnd_4785442 := by
    simpa [prefixWord, tailWord_4785442, baseEnd_4785442] using wordTrace_append hprefix tailTrace_4785442
  have hstable : (prefixWord ++ tailWord_4785442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4785442).length < 2 ^ (prefixWord ++ tailWord_4785442).sum := by decide
  have hdescent : baseEnd_4785442 < baseStart_4785442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4785442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4785453 : List Nat := [1, 5, 3, 1, 1, 1, 3, 3, 1, 2, 2]
def baseStart_4785453 : Nat := 118140960795 + 4785453 * 2 ^ 59
def prefixEnd_4785453 : Nat := 4983230072969 + 3 ^ 40 * 4785453 * 2
def baseEnd_4785453 : Nat := 2457237538500370626829609

theorem tailTrace_4785453 : CollatzResearch.WordTrace tailWord_4785453 prefixEnd_4785453 2457237538500370626829609 := by
  unfold tailWord_4785453
  simp only [CollatzResearch.WordTrace]
  refine ⟨174539809932128546149705013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116359873288085697433136675 174539809932128546149705013)
  ·
    refine ⟨16363107181137051201534845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 174539809932128546149705013 16363107181137051201534845)
    ·
      refine ⟨6136165192926394200575567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16363107181137051201534845 6136165192926394200575567)
      ·
        refine ⟨9204247789389591300863351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6136165192926394200575567 9204247789389591300863351)
        ·
          refine ⟨13806371684084386951295027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9204247789389591300863351 13806371684084386951295027)
          ·
            refine ⟨20709557526126580426942541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13806371684084386951295027 20709557526126580426942541)
            ·
              refine ⟨7766084072297467660103453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20709557526126580426942541 7766084072297467660103453)
              ·
                refine ⟨2912281527111550372538795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7766084072297467660103453 2912281527111550372538795)
                ·
                  refine ⟨4368422290667325558808193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2912281527111550372538795 4368422290667325558808193)
                  ·
                    refine ⟨3276316718000494169106145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4368422290667325558808193 3276316718000494169106145)
                    ·
                      refine ⟨2457237538500370626829609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3276316718000494169106145 2457237538500370626829609)
                      ·
                        rfl

theorem cell23_4785453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_4785453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4785453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4785453 prefixEnd_4785453 := by exact prefixLift 4785453
  have htrace : WordTrace (prefixWord ++ tailWord_4785453) baseStart_4785453 baseEnd_4785453 := by
    simpa [prefixWord, tailWord_4785453, baseEnd_4785453] using wordTrace_append hprefix tailTrace_4785453
  have hstable : (prefixWord ++ tailWord_4785453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4785453).length < 2 ^ (prefixWord ++ tailWord_4785453).sum := by decide
  have hdescent : baseEnd_4785453 < baseStart_4785453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4785453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4785488 : List Nat := [2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 4]
def baseStart_4785488 : Nat := 118140960795 + 4785488 * 2 ^ 59
def prefixEnd_4785488 : Nat := 4983230072969 + 3 ^ 40 * 4785488 * 2
def baseEnd_4785488 : Nat := 2457255510323277989891947

theorem tailTrace_4785488 : CollatzResearch.WordTrace tailWord_4785488 prefixEnd_4785488 2457255510323277989891947 := by
  unfold tailWord_4785488
  simp only [CollatzResearch.WordTrace]
  refine ⟨87270543243500873563614559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116360724324667831418152745 87270543243500873563614559)
  ·
    refine ⟨130905814865251310345421839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87270543243500873563614559 130905814865251310345421839)
    ·
      refine ⟨196358722297876965518132759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130905814865251310345421839 196358722297876965518132759)
      ·
        refine ⟨294538083446815448277199139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196358722297876965518132759 294538083446815448277199139)
        ·
          refine ⟨441807125170223172415798709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294538083446815448277199139 441807125170223172415798709)
          ·
            refine ⟨41419417984708422413981129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 441807125170223172415798709 41419417984708422413981129)
            ·
              refine ⟨31064563488531316810485847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41419417984708422413981129 31064563488531316810485847)
              ·
                refine ⟨46596845232796975215728771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31064563488531316810485847 46596845232796975215728771)
                ·
                  refine ⟨69895267849195462823593157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46596845232796975215728771 69895267849195462823593157)
                  ·
                    refine ⟨13105362721724149279423717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 69895267849195462823593157 13105362721724149279423717)
                    ·
                      refine ⟨2457255510323277989891947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13105362721724149279423717 2457255510323277989891947)
                      ·
                        rfl

theorem cell23_4785488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 4].length) (baseStart_4785488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4785488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4785488 prefixEnd_4785488 := by exact prefixLift 4785488
  have htrace : WordTrace (prefixWord ++ tailWord_4785488) baseStart_4785488 baseEnd_4785488 := by
    simpa [prefixWord, tailWord_4785488, baseEnd_4785488] using wordTrace_append hprefix tailTrace_4785488
  have hstable : (prefixWord ++ tailWord_4785488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4785488).length < 2 ^ (prefixWord ++ tailWord_4785488).sum := by decide
  have hdescent : baseEnd_4785488 < baseStart_4785488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4785488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4785492 : List Nat := [2, 4, 1, 1, 2, 1, 2, 3, 1, 4, 2]
def baseStart_4785492 : Nat := 118140960795 + 4785492 * 2 ^ 59
def prefixEnd_4785492 : Nat := 4983230072969 + 3 ^ 40 * 4785492 * 2
def baseEnd_4785492 : Nat := 2457257564245895974241929

theorem tailTrace_4785492 : CollatzResearch.WordTrace tailWord_4785492 prefixEnd_4785492 2457257564245895974241929 := by
  unfold tailWord_4785492
  simp only [CollatzResearch.WordTrace]
  refine ⟨87270616189493627905187365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116360821585991503873583153 87270616189493627905187365)
  ·
    refine ⟨16363240535530055232222631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87270616189493627905187365 16363240535530055232222631)
    ·
      refine ⟨24544860803295082848333947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16363240535530055232222631 24544860803295082848333947)
      ·
        refine ⟨36817291204942624272500921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24544860803295082848333947 36817291204942624272500921)
        ·
          refine ⟨27612968403706968204375691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36817291204942624272500921 27612968403706968204375691)
          ·
            refine ⟨41419452605560452306563537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27612968403706968204375691 41419452605560452306563537)
            ·
              refine ⟨31064589454170339229922653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41419452605560452306563537 31064589454170339229922653)
              ·
                refine ⟨11649221045313877211220995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31064589454170339229922653 11649221045313877211220995)
                ·
                  refine ⟨17473831567970815816831493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11649221045313877211220995 17473831567970815816831493)
                  ·
                    refine ⟨3276343418994527965655905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17473831567970815816831493 3276343418994527965655905)
                    ·
                      refine ⟨2457257564245895974241929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3276343418994527965655905 2457257564245895974241929)
                      ·
                        rfl

theorem cell23_4785492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 1, 4, 2].length) (baseStart_4785492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4785492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4785492 prefixEnd_4785492 := by exact prefixLift 4785492
  have htrace : WordTrace (prefixWord ++ tailWord_4785492) baseStart_4785492 baseEnd_4785492 := by
    simpa [prefixWord, tailWord_4785492, baseEnd_4785492] using wordTrace_append hprefix tailTrace_4785492
  have hstable : (prefixWord ++ tailWord_4785492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4785492).length < 2 ^ (prefixWord ++ tailWord_4785492).sum := by decide
  have hdescent : baseEnd_4785492 < baseStart_4785492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4785492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4785498 : List Nat := [3, 1, 1, 2, 1, 2, 2, 4, 7]
def baseStart_4785498 : Nat := 118140960795 + 4785498 * 2 ^ 59
def prefixEnd_4785498 : Nat := 4983230072969 + 3 ^ 40 * 4785498 * 2
def baseEnd_4785498 : Nat := 273028960569980327862989

theorem tailTrace_4785498 : CollatzResearch.WordTrace tailWord_4785498 prefixEnd_4785498 273028960569980327862989 := by
  unfold tailWord_4785498
  simp only [CollatzResearch.WordTrace]
  refine ⟨43635362804241379708773287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116360967477977012556728765 43635362804241379708773287)
  ·
    refine ⟨65453044206362069563159931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43635362804241379708773287 65453044206362069563159931)
    ·
      refine ⟨98179566309543104344739897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65453044206362069563159931 98179566309543104344739897)
      ·
        refine ⟨73634674732157328258554923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98179566309543104344739897 73634674732157328258554923)
        ·
          refine ⟨110452012098235992387832385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73634674732157328258554923 110452012098235992387832385)
          ·
            refine ⟨82839009073676994290874289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110452012098235992387832385 82839009073676994290874289)
            ·
              refine ⟨62129256805257745718155717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82839009073676994290874289 62129256805257745718155717)
              ·
                refine ⟨11649235650985827322154197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62129256805257745718155717 11649235650985827322154197)
                ·
                  refine ⟨273028960569980327862989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11649235650985827322154197 273028960569980327862989)
                  ·
                    rfl

theorem cell23_4785498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 7].length) (baseStart_4785498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4785498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4785498 prefixEnd_4785498 := by exact prefixLift 4785498
  have htrace : WordTrace (prefixWord ++ tailWord_4785498) baseStart_4785498 baseEnd_4785498 := by
    simpa [prefixWord, tailWord_4785498, baseEnd_4785498] using wordTrace_append hprefix tailTrace_4785498
  have hstable : (prefixWord ++ tailWord_4785498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4785498).length < 2 ^ (prefixWord ++ tailWord_4785498).sum := by decide
  have hdescent : baseEnd_4785498 < baseStart_4785498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4785498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
