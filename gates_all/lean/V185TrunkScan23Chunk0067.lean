import V185TrunkScan23Chunk0066

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_397042 : List Nat := [3, 2, 1, 3, 1, 1, 3, 2, 1, 1, 5]
def baseStart_397042 : Nat := 118140960795 + 397042 * 2 ^ 59
def prefixEnd_397042 : Nat := 4983230072969 + 3 ^ 40 * 397042 * 2
def baseEnd_397042 : Nat := 203873386022540805049043

theorem tailTrace_397042 : CollatzResearch.WordTrace tailWord_397042 prefixEnd_397042 203873386022540805049043 := by
  unfold tailWord_397042
  simp only [CollatzResearch.WordTrace]
  refine ⟨3620327856898029555032345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9654207618394745480086253 3620327856898029555032345)
  ·
    refine ⟨2715245892673522166274259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3620327856898029555032345 2715245892673522166274259)
    ·
      refine ⟨4072868839010283249411389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2715245892673522166274259 4072868839010283249411389)
      ·
        refine ⟨1527325814628856218529271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4072868839010283249411389 1527325814628856218529271)
        ·
          refine ⟨2290988721943284327793907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1527325814628856218529271 2290988721943284327793907)
          ·
            refine ⟨3436483082914926491690861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2290988721943284327793907 3436483082914926491690861)
            ·
              refine ⟨1288681156093097434384073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3436483082914926491690861 1288681156093097434384073)
              ·
                refine ⟨966510867069823075788055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1288681156093097434384073 966510867069823075788055)
                ·
                  refine ⟨1449766300604734613682083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 966510867069823075788055 1449766300604734613682083)
                  ·
                    refine ⟨2174649450907101920523125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1449766300604734613682083 2174649450907101920523125)
                    ·
                      refine ⟨203873386022540805049043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2174649450907101920523125 203873386022540805049043)
                      ·
                        rfl

theorem cell23_397042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_397042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397042 prefixEnd_397042 := by exact prefixLift 397042
  have htrace : WordTrace (prefixWord ++ tailWord_397042) baseStart_397042 baseEnd_397042 := by
    simpa [prefixWord, tailWord_397042, baseEnd_397042] using wordTrace_append hprefix tailTrace_397042
  have hstable : (prefixWord ++ tailWord_397042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397042).length < 2 ^ (prefixWord ++ tailWord_397042).sum := by decide
  have hdescent : baseEnd_397042 < baseStart_397042 := by decide
  rcases family_descends (prefixWord ++ tailWord_397042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397089 : List Nat := [1, 2, 3, 2, 1, 3, 2, 1, 4, 1, 3]
def baseStart_397089 : Nat := 118140960795 + 397089 * 2 ^ 59
def prefixEnd_397089 : Nat := 4983230072969 + 3 ^ 40 * 397089 * 2
def baseEnd_397089 : Nat := 203897519613302121161327

theorem tailTrace_397089 : CollatzResearch.WordTrace tailWord_397089 prefixEnd_397089 203897519613302121161327 := by
  unfold tailWord_397089
  simp only [CollatzResearch.WordTrace]
  refine ⟨14483025658421845247090321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9655350438947896831393547 14483025658421845247090321)
  ·
    refine ⟨10862269243816383935317741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14483025658421845247090321 10862269243816383935317741)
    ·
      refine ⟨4073350966431143975744153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10862269243816383935317741 4073350966431143975744153)
      ·
        refine ⟨3055013224823357981808115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4073350966431143975744153 3055013224823357981808115)
        ·
          refine ⟨4582519837235036972712173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3055013224823357981808115 4582519837235036972712173)
          ·
            refine ⟨1718444938963138864767065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4582519837235036972712173 1718444938963138864767065)
            ·
              refine ⟨1288833704222354148575299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1718444938963138864767065 1288833704222354148575299)
              ·
                refine ⟨1933250556333531222862949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1288833704222354148575299 1933250556333531222862949)
                ·
                  refine ⟨362484479312537104286803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1933250556333531222862949 362484479312537104286803)
                  ·
                    refine ⟨543726718968805656430205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 362484479312537104286803 543726718968805656430205)
                    ·
                      refine ⟨203897519613302121161327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 543726718968805656430205 203897519613302121161327)
                      ·
                        rfl

theorem cell23_397089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_397089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397089 prefixEnd_397089 := by exact prefixLift 397089
  have htrace : WordTrace (prefixWord ++ tailWord_397089) baseStart_397089 baseEnd_397089 := by
    simpa [prefixWord, tailWord_397089, baseEnd_397089] using wordTrace_append hprefix tailTrace_397089
  have hstable : (prefixWord ++ tailWord_397089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397089).length < 2 ^ (prefixWord ++ tailWord_397089).sum := by decide
  have hdescent : baseEnd_397089 < baseStart_397089 := by decide
  rcases family_descends (prefixWord ++ tailWord_397089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397090 : List Nat := [3, 3, 1, 1, 2, 1, 5, 2, 1, 2, 2]
def baseStart_397090 : Nat := 118140960795 + 397090 * 2 ^ 59
def prefixEnd_397090 : Nat := 4983230072969 + 3 ^ 40 * 397090 * 2
def baseEnd_397090 : Nat := 203898033093956617248823

theorem tailTrace_397090 : CollatzResearch.WordTrace tailWord_397090 prefixEnd_397090 203898033093956617248823 := by
  unfold tailWord_397090
  simp only [CollatzResearch.WordTrace]
  refine ⟨3620765532854555604469181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9655374754278814945251149 3620765532854555604469181)
  ·
    refine ⟨1357787074820458351675943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3620765532854555604469181 1357787074820458351675943)
    ·
      refine ⟨2036680612230687527513915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1357787074820458351675943 2036680612230687527513915)
      ·
        refine ⟨3055020918346031291270873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2036680612230687527513915 3055020918346031291270873)
        ·
          refine ⟨2291265688759523468453155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3055020918346031291270873 2291265688759523468453155)
          ·
            refine ⟨3436898533139285202679733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2291265688759523468453155 3436898533139285202679733)
            ·
              refine ⟨322209237481807987751225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3436898533139285202679733 322209237481807987751225)
              ·
                refine ⟨241656928111355990813419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 322209237481807987751225 241656928111355990813419)
                ·
                  refine ⟨362485392167033986220129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 241656928111355990813419 362485392167033986220129)
                  ·
                    refine ⟨271864044125275489665097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 362485392167033986220129 271864044125275489665097)
                    ·
                      refine ⟨203898033093956617248823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 271864044125275489665097 203898033093956617248823)
                      ·
                        rfl

theorem cell23_397090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 2, 1, 2, 2].length) (baseStart_397090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397090 prefixEnd_397090 := by exact prefixLift 397090
  have htrace : WordTrace (prefixWord ++ tailWord_397090) baseStart_397090 baseEnd_397090 := by
    simpa [prefixWord, tailWord_397090, baseEnd_397090] using wordTrace_append hprefix tailTrace_397090
  have hstable : (prefixWord ++ tailWord_397090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397090).length < 2 ^ (prefixWord ++ tailWord_397090).sum := by decide
  have hdescent : baseEnd_397090 < baseStart_397090 := by decide
  rcases family_descends (prefixWord ++ tailWord_397090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397106 : List Nat := [3, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3]
def baseStart_397106 : Nat := 118140960795 + 397106 * 2 ^ 59
def prefixEnd_397106 : Nat := 4983230072969 + 3 ^ 40 * 397106 * 2
def baseEnd_397106 : Nat := 203906248784428554648749

theorem tailTrace_397106 : CollatzResearch.WordTrace tailWord_397106 prefixEnd_397106 203906248784428554648749 := by
  unfold tailWord_397106
  simp only [CollatzResearch.WordTrace]
  refine ⟨3620911424840064287614793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9655763799573504766972781 3620911424840064287614793)
  ·
    refine ⟨2715683568630048215711095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3620911424840064287614793 2715683568630048215711095)
    ·
      refine ⟨4073525352945072323566643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2715683568630048215711095 4073525352945072323566643)
      ·
        refine ⟨6110288029417608485349965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4073525352945072323566643 6110288029417608485349965)
        ·
          refine ⟨2291358011031603182006237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6110288029417608485349965 2291358011031603182006237)
          ·
            refine ⟨859259254136851193252339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2291358011031603182006237 859259254136851193252339)
            ·
              refine ⟨1288888881205276789878509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 859259254136851193252339 1288888881205276789878509)
              ·
                refine ⟨483333330451978796204441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1288888881205276789878509 483333330451978796204441)
                ·
                  refine ⟨362499997838984097153331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 483333330451978796204441 362499997838984097153331)
                  ·
                    refine ⟨543749996758476145729997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 362499997838984097153331 543749996758476145729997)
                    ·
                      refine ⟨203906248784428554648749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 543749996758476145729997 203906248784428554648749)
                      ·
                        rfl

theorem cell23_397106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3].length) (baseStart_397106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397106 prefixEnd_397106 := by exact prefixLift 397106
  have htrace : WordTrace (prefixWord ++ tailWord_397106) baseStart_397106 baseEnd_397106 := by
    simpa [prefixWord, tailWord_397106, baseEnd_397106] using wordTrace_append hprefix tailTrace_397106
  have hstable : (prefixWord ++ tailWord_397106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397106).length < 2 ^ (prefixWord ++ tailWord_397106).sum := by decide
  have hdescent : baseEnd_397106 < baseStart_397106 := by decide
  rcases family_descends (prefixWord ++ tailWord_397106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397116 : List Nat := [2, 2, 2, 2, 1, 1, 5, 2, 1, 3, 2]
def baseStart_397116 : Nat := 118140960795 + 397116 * 2 ^ 59
def prefixEnd_397116 : Nat := 4983230072969 + 3 ^ 40 * 397116 * 2
def baseEnd_397116 : Nat := 203911383590973515523703

theorem tailTrace_397116 : CollatzResearch.WordTrace tailWord_397116 prefixEnd_397116 203911383590973515523703 := by
  unfold tailWord_397116
  simp only [CollatzResearch.WordTrace]
  refine ⟨7242005214662014429161601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9656006952882685905548801 7242005214662014429161601)
  ·
    refine ⟨5431503910996510821871201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7242005214662014429161601 5431503910996510821871201)
    ·
      refine ⟨4073627933247383116403401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5431503910996510821871201 4073627933247383116403401)
      ·
        refine ⟨3055220949935537337302551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4073627933247383116403401 3055220949935537337302551)
        ·
          refine ⟨4582831424903306005953827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3055220949935537337302551 4582831424903306005953827)
          ·
            refine ⟨6874247137354959008930741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4582831424903306005953827 6874247137354959008930741)
            ·
              refine ⟨644460669127027407087257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6874247137354959008930741 644460669127027407087257)
              ·
                refine ⟨483345501845270555315443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 644460669127027407087257 483345501845270555315443)
                ·
                  refine ⟨725018252767905832973165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 483345501845270555315443 725018252767905832973165)
                  ·
                    refine ⟨271881844787964687364937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 725018252767905832973165 271881844787964687364937)
                    ·
                      refine ⟨203911383590973515523703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 271881844787964687364937 203911383590973515523703)
                      ·
                        rfl

theorem cell23_397116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2, 1, 3, 2].length) (baseStart_397116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397116 prefixEnd_397116 := by exact prefixLift 397116
  have htrace : WordTrace (prefixWord ++ tailWord_397116) baseStart_397116 baseEnd_397116 := by
    simpa [prefixWord, tailWord_397116, baseEnd_397116] using wordTrace_append hprefix tailTrace_397116
  have hstable : (prefixWord ++ tailWord_397116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397116).length < 2 ^ (prefixWord ++ tailWord_397116).sum := by decide
  have hdescent : baseEnd_397116 < baseStart_397116 := by decide
  rcases family_descends (prefixWord ++ tailWord_397116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397129 : List Nat := [1, 2, 1, 1, 2, 4, 3, 2, 1, 4, 2]
def baseStart_397129 : Nat := 118140960795 + 397129 * 2 ^ 59
def prefixEnd_397129 : Nat := 4983230072969 + 3 ^ 40 * 397129 * 2
def baseEnd_397129 : Nat := 203918058839481964661143

theorem tailTrace_397129 : CollatzResearch.WordTrace tailWord_397129 prefixEnd_397129 203918058839481964661143 := by
  unfold tailWord_397129
  simp only [CollatzResearch.WordTrace]
  refine ⟨14484484578276932078546441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9656323052184621385697627 14484484578276932078546441)
  ·
    refine ⟨10863363433707699058909831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14484484578276932078546441 10863363433707699058909831)
    ·
      refine ⟨16295045150561548588364747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10863363433707699058909831 16295045150561548588364747)
      ·
        refine ⟨24442567725842322882547121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16295045150561548588364747 24442567725842322882547121)
        ·
          refine ⟨18331925794381742161910341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24442567725842322882547121 18331925794381742161910341)
          ·
            refine ⟨3437236086446576655358189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18331925794381742161910341 3437236086446576655358189)
            ·
              refine ⟨1288963532417466245759321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3437236086446576655358189 1288963532417466245759321)
              ·
                refine ⟨966722649313099684319491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1288963532417466245759321 966722649313099684319491)
                ·
                  refine ⟨1450083973969649526479237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 966722649313099684319491 1450083973969649526479237)
                  ·
                    refine ⟨271890745119309286214857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1450083973969649526479237 271890745119309286214857)
                    ·
                      refine ⟨203918058839481964661143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 271890745119309286214857 203918058839481964661143)
                      ·
                        rfl

theorem cell23_397129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 4, 2].length) (baseStart_397129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397129 prefixEnd_397129 := by exact prefixLift 397129
  have htrace : WordTrace (prefixWord ++ tailWord_397129) baseStart_397129 baseEnd_397129 := by
    simpa [prefixWord, tailWord_397129, baseEnd_397129] using wordTrace_append hprefix tailTrace_397129
  have hstable : (prefixWord ++ tailWord_397129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397129).length < 2 ^ (prefixWord ++ tailWord_397129).sum := by decide
  have hdescent : baseEnd_397129 < baseStart_397129 := by decide
  rcases family_descends (prefixWord ++ tailWord_397129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397214 : List Nat := [4, 3, 1, 3, 1, 1, 3, 1, 2, 2, 2]
def baseStart_397214 : Nat := 118140960795 + 397214 * 2 ^ 59
def prefixEnd_397214 : Nat := 4983230072969 + 3 ^ 40 * 397214 * 2
def baseEnd_397214 : Nat := 203961704695114132098253

theorem tailTrace_397214 : CollatzResearch.WordTrace tailWord_397214 prefixEnd_397214 203961704695114132098253 := by
  unfold tailWord_397214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1810948097871123949423837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9658389855312661063593797 1810948097871123949423837)
  ·
    refine ⟨679105536701671481033939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1810948097871123949423837 679105536701671481033939)
    ·
      refine ⟨1018658305052507221550909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 679105536701671481033939 1018658305052507221550909)
      ·
        refine ⟨381996864394690208081591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1018658305052507221550909 381996864394690208081591)
        ·
          refine ⟨572995296592035312122387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381996864394690208081591 572995296592035312122387)
          ·
            refine ⟨859492944888052968183581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 572995296592035312122387 859492944888052968183581)
            ·
              refine ⟨322309854333019863068843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 859492944888052968183581 322309854333019863068843)
              ·
                refine ⟨483464781499529794603265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322309854333019863068843 483464781499529794603265)
                ·
                  refine ⟨362598586124647345952449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 483464781499529794603265 362598586124647345952449)
                  ·
                    refine ⟨271948939593485509464337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 362598586124647345952449 271948939593485509464337)
                    ·
                      refine ⟨203961704695114132098253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 271948939593485509464337 203961704695114132098253)
                      ·
                        rfl

theorem cell23_397214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_397214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397214 prefixEnd_397214 := by exact prefixLift 397214
  have htrace : WordTrace (prefixWord ++ tailWord_397214) baseStart_397214 baseEnd_397214 := by
    simpa [prefixWord, tailWord_397214, baseEnd_397214] using wordTrace_append hprefix tailTrace_397214
  have hstable : (prefixWord ++ tailWord_397214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397214).length < 2 ^ (prefixWord ++ tailWord_397214).sum := by decide
  have hdescent : baseEnd_397214 < baseStart_397214 := by decide
  rcases family_descends (prefixWord ++ tailWord_397214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397239 : List Nat := [1, 1, 3, 1, 3, 1, 1, 5, 2, 2, 3]
def baseStart_397239 : Nat := 118140960795 + 397239 * 2 ^ 59
def prefixEnd_397239 : Nat := 4983230072969 + 3 ^ 40 * 397239 * 2
def baseEnd_397239 : Nat := 203974541711476534285637

theorem tailTrace_397239 : CollatzResearch.WordTrace tailWord_397239 prefixEnd_397239 203974541711476534285637 := by
  unfold tailWord_397239
  simp only [CollatzResearch.WordTrace]
  refine ⟨14488496607878420865050771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9658997738585613910033847 14488496607878420865050771)
  ·
    refine ⟨21732744911817631297576157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14488496607878420865050771 21732744911817631297576157)
    ·
      refine ⟨8149779341931611736591059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21732744911817631297576157 8149779341931611736591059)
      ·
        refine ⟨12224669012897417604886589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8149779341931611736591059 12224669012897417604886589)
        ·
          refine ⟨4584250879836531601832471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12224669012897417604886589 4584250879836531601832471)
          ·
            refine ⟨6876376319754797402748707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4584250879836531601832471 6876376319754797402748707)
            ·
              refine ⟨10314564479632196104123061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6876376319754797402748707 10314564479632196104123061)
              ·
                refine ⟨966990419965518384761537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10314564479632196104123061 966990419965518384761537)
                ·
                  refine ⟨725242814974138788571153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 966990419965518384761537 725242814974138788571153)
                  ·
                    refine ⟨543932111230604091428365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 725242814974138788571153 543932111230604091428365)
                    ·
                      refine ⟨203974541711476534285637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 543932111230604091428365 203974541711476534285637)
                      ·
                        rfl

theorem cell23_397239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2, 2, 3].length) (baseStart_397239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397239 prefixEnd_397239 := by exact prefixLift 397239
  have htrace : WordTrace (prefixWord ++ tailWord_397239) baseStart_397239 baseEnd_397239 := by
    simpa [prefixWord, tailWord_397239, baseEnd_397239] using wordTrace_append hprefix tailTrace_397239
  have hstable : (prefixWord ++ tailWord_397239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397239).length < 2 ^ (prefixWord ++ tailWord_397239).sum := by decide
  have hdescent : baseEnd_397239 < baseStart_397239 := by decide
  rcases family_descends (prefixWord ++ tailWord_397239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397256 : List Nat := [2, 1, 3, 1, 4, 2, 1, 2, 2, 2, 3]
def baseStart_397256 : Nat := 118140960795 + 397256 * 2 ^ 59
def prefixEnd_397256 : Nat := 4983230072969 + 3 ^ 40 * 397256 * 2
def baseEnd_397256 : Nat := 203983270882602967773059

theorem tailTrace_397256 : CollatzResearch.WordTrace tailWord_397256 prefixEnd_397256 203983270882602967773059 := by
  unfold tailWord_397256
  simp only [CollatzResearch.WordTrace]
  refine ⟨7244558324408416384209811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9659411099211221845613081 7244558324408416384209811)
  ·
    refine ⟨10866837486612624576314717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7244558324408416384209811 10866837486612624576314717)
    ·
      refine ⟨4075064057479734216118019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10866837486612624576314717 4075064057479734216118019)
      ·
        refine ⟨6112596086219601324177029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4075064057479734216118019 6112596086219601324177029)
        ·
          refine ⟨1146111766166175248283193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6112596086219601324177029 1146111766166175248283193)
          ·
            refine ⟨859583824624631436212395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1146111766166175248283193 859583824624631436212395)
            ·
              refine ⟨1289375736936947154318593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 859583824624631436212395 1289375736936947154318593)
              ·
                refine ⟨967031802702710365738945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1289375736936947154318593 967031802702710365738945)
                ·
                  refine ⟨725273852027032774304209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 967031802702710365738945 725273852027032774304209)
                  ·
                    refine ⟨543955389020274580728157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 725273852027032774304209 543955389020274580728157)
                    ·
                      refine ⟨203983270882602967773059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 543955389020274580728157 203983270882602967773059)
                      ·
                        rfl

theorem cell23_397256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 2, 2, 3].length) (baseStart_397256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397256 prefixEnd_397256 := by exact prefixLift 397256
  have htrace : WordTrace (prefixWord ++ tailWord_397256) baseStart_397256 baseEnd_397256 := by
    simpa [prefixWord, tailWord_397256, baseEnd_397256] using wordTrace_append hprefix tailTrace_397256
  have hstable : (prefixWord ++ tailWord_397256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397256).length < 2 ^ (prefixWord ++ tailWord_397256).sum := by decide
  have hdescent : baseEnd_397256 < baseStart_397256 := by decide
  rcases family_descends (prefixWord ++ tailWord_397256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397263 : List Nat := [1, 1, 2, 1, 1, 5, 5, 2, 1, 4]
def baseStart_397263 : Nat := 118140960795 + 397263 * 2 ^ 59
def prefixEnd_397263 : Nat := 4983230072969 + 3 ^ 40 * 397263 * 2
def baseEnd_397263 : Nat := 67995621749061480128509

theorem tailTrace_397263 : CollatzResearch.WordTrace tailWord_397263 prefixEnd_397263 67995621749061480128509 := by
  unfold tailWord_397263
  simp only [CollatzResearch.WordTrace]
  refine ⟨14489371959791472963924443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9659581306527648642616295 14489371959791472963924443)
  ·
    refine ⟨21734057939687209445886665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14489371959791472963924443 21734057939687209445886665)
    ·
      refine ⟨16300543454765407084414999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21734057939687209445886665 16300543454765407084414999)
      ·
        refine ⟨24450815182148110626622499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16300543454765407084414999 24450815182148110626622499)
        ·
          refine ⟨36676222773222165939933749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24450815182148110626622499 36676222773222165939933749)
          ·
            refine ⟨3438395884989578056868789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36676222773222165939933749 3438395884989578056868789)
            ·
              refine ⟨322349614217772942831449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3438395884989578056868789 322349614217772942831449)
              ·
                refine ⟨241762210663329707123587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 322349614217772942831449 241762210663329707123587)
                ·
                  refine ⟨362643315994994560685381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 241762210663329707123587 362643315994994560685381)
                  ·
                    refine ⟨67995621749061480128509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 362643315994994560685381 67995621749061480128509)
                    ·
                      rfl

theorem cell23_397263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 2, 1, 4].length) (baseStart_397263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397263 prefixEnd_397263 := by exact prefixLift 397263
  have htrace : WordTrace (prefixWord ++ tailWord_397263) baseStart_397263 baseEnd_397263 := by
    simpa [prefixWord, tailWord_397263, baseEnd_397263] using wordTrace_append hprefix tailTrace_397263
  have hstable : (prefixWord ++ tailWord_397263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397263).length < 2 ^ (prefixWord ++ tailWord_397263).sum := by decide
  have hdescent : baseEnd_397263 < baseStart_397263 := by decide
  rcases family_descends (prefixWord ++ tailWord_397263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397296 : List Nat := [2, 1, 1, 1, 3, 2, 3, 3, 2, 3, 2]
def baseStart_397296 : Nat := 118140960795 + 397296 * 2 ^ 59
def prefixEnd_397296 : Nat := 4983230072969 + 3 ^ 40 * 397296 * 2
def baseEnd_397296 : Nat := 204003810108782811272875

theorem tailTrace_397296 : CollatzResearch.WordTrace tailWord_397296 prefixEnd_397296 204003810108782811272875 := by
  unfold tailWord_397296
  simp only [CollatzResearch.WordTrace]
  refine ⟨7245287784335959799937871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9660383712447946399917161 7245287784335959799937871)
  ·
    refine ⟨10867931676503939699906807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7245287784335959799937871 10867931676503939699906807)
    ·
      refine ⟨16301897514755909549860211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10867931676503939699906807 16301897514755909549860211)
      ·
        refine ⟨24452846272133864324790317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16301897514755909549860211 24452846272133864324790317)
        ·
          refine ⟨9169817352050199121796369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24452846272133864324790317 9169817352050199121796369)
          ·
            refine ⟨6877363014037649341347277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9169817352050199121796369 6877363014037649341347277)
            ·
              refine ⟨2579011130264118503005229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6877363014037649341347277 2579011130264118503005229)
              ·
                refine ⟨967129173849044438626961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2579011130264118503005229 967129173849044438626961)
                ·
                  refine ⟨725346880386783328970221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 967129173849044438626961 725346880386783328970221)
                  ·
                    refine ⟨272005080145043748363833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 725346880386783328970221 272005080145043748363833)
                    ·
                      refine ⟨204003810108782811272875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 272005080145043748363833 204003810108782811272875)
                      ·
                        rfl

theorem cell23_397296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 2, 3, 2].length) (baseStart_397296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397296 prefixEnd_397296 := by exact prefixLift 397296
  have htrace : WordTrace (prefixWord ++ tailWord_397296) baseStart_397296 baseEnd_397296 := by
    simpa [prefixWord, tailWord_397296, baseEnd_397296] using wordTrace_append hprefix tailTrace_397296
  have hstable : (prefixWord ++ tailWord_397296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397296).length < 2 ^ (prefixWord ++ tailWord_397296).sum := by decide
  have hdescent : baseEnd_397296 < baseStart_397296 := by decide
  rcases family_descends (prefixWord ++ tailWord_397296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397336 : List Nat := [2, 1, 2, 3, 2, 1, 1, 5, 2, 4]
def baseStart_397336 : Nat := 118140960795 + 397336 * 2 ^ 59
def prefixEnd_397336 : Nat := 4983230072969 + 3 ^ 40 * 397336 * 2
def baseEnd_397336 : Nat := 68008116444987551590897

theorem tailTrace_397336 : CollatzResearch.WordTrace tailWord_397336 prefixEnd_397336 68008116444987551590897 := by
  unfold tailWord_397336
  simp only [CollatzResearch.WordTrace]
  refine ⟨7246017244263503215665931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9661356325684670954221241 7246017244263503215665931)
  ·
    refine ⟨10869025866395254823498897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7246017244263503215665931 10869025866395254823498897)
    ·
      refine ⟨8151769399796441117624173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10869025866395254823498897 8151769399796441117624173)
      ·
        refine ⟨3056913524923665419109065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8151769399796441117624173 3056913524923665419109065)
        ·
          refine ⟨2292685143692749064331799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3056913524923665419109065 2292685143692749064331799)
          ·
            refine ⟨3439027715539123596497699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2292685143692749064331799 3439027715539123596497699)
            ·
              refine ⟨5158541573308685394746549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3439027715539123596497699 5158541573308685394746549)
              ·
                refine ⟨483613272497689255757489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5158541573308685394746549 483613272497689255757489)
                ·
                  refine ⟨362709954373266941818117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 483613272497689255757489 362709954373266941818117)
                  ·
                    refine ⟨68008116444987551590897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 362709954373266941818117 68008116444987551590897)
                    ·
                      rfl

theorem cell23_397336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5, 2, 4].length) (baseStart_397336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397336 prefixEnd_397336 := by exact prefixLift 397336
  have htrace : WordTrace (prefixWord ++ tailWord_397336) baseStart_397336 baseEnd_397336 := by
    simpa [prefixWord, tailWord_397336, baseEnd_397336] using wordTrace_append hprefix tailTrace_397336
  have hstable : (prefixWord ++ tailWord_397336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397336).length < 2 ^ (prefixWord ++ tailWord_397336).sum := by decide
  have hdescent : baseEnd_397336 < baseStart_397336 := by decide
  rcases family_descends (prefixWord ++ tailWord_397336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397343 : List Nat := [1, 1, 2, 4, 1, 2, 3, 2, 3, 2, 2]
def baseStart_397343 : Nat := 118140960795 + 397343 * 2 ^ 59
def prefixEnd_397343 : Nat := 4983230072969 + 3 ^ 40 * 397343 * 2
def baseEnd_397343 : Nat := 204027943699544127385159

theorem tailTrace_397343 : CollatzResearch.WordTrace tailWord_397343 prefixEnd_397343 204027943699544127385159 := by
  unfold tailWord_397343
  simp only [CollatzResearch.WordTrace]
  refine ⟨14492289799501646626836683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9661526533001097751224455 14492289799501646626836683)
  ·
    refine ⟨21738434699252469940255025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14492289799501646626836683 21738434699252469940255025)
    ·
      refine ⟨16303826024439352455191269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21738434699252469940255025 16303826024439352455191269)
      ·
        refine ⟨3056967379582378585348363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16303826024439352455191269 3056967379582378585348363)
        ·
          refine ⟨4585451069373567878022545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3056967379582378585348363 4585451069373567878022545)
          ·
            refine ⟨3439088302030175908516909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4585451069373567878022545 3439088302030175908516909)
            ·
              refine ⟨1289658113261315965693841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3439088302030175908516909 1289658113261315965693841)
              ·
                refine ⟨967243584945986974270381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1289658113261315965693841 967243584945986974270381)
                ·
                  refine ⟨362716344354745115351393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 967243584945986974270381 362716344354745115351393)
                  ·
                    refine ⟨272037258266058836513545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 362716344354745115351393 272037258266058836513545)
                    ·
                      refine ⟨204027943699544127385159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 272037258266058836513545 204027943699544127385159)
                      ·
                        rfl

theorem cell23_397343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 3, 2, 2].length) (baseStart_397343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397343 prefixEnd_397343 := by exact prefixLift 397343
  have htrace : WordTrace (prefixWord ++ tailWord_397343) baseStart_397343 baseEnd_397343 := by
    simpa [prefixWord, tailWord_397343, baseEnd_397343] using wordTrace_append hprefix tailTrace_397343
  have hstable : (prefixWord ++ tailWord_397343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397343).length < 2 ^ (prefixWord ++ tailWord_397343).sum := by decide
  have hdescent : baseEnd_397343 < baseStart_397343 := by decide
  rcases family_descends (prefixWord ++ tailWord_397343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397346 : List Nat := [3, 3, 1, 1, 1, 2, 1, 3, 3, 2, 3]
def baseStart_397346 : Nat := 118140960795 + 397346 * 2 ^ 59
def prefixEnd_397346 : Nat := 4983230072969 + 3 ^ 40 * 397346 * 2
def baseEnd_397346 : Nat := 204029484141507615647645

theorem tailTrace_397346 : CollatzResearch.WordTrace tailWord_397346 prefixEnd_397346 204029484141507615647645 := by
  unfold tailWord_397346
  simp only [CollatzResearch.WordTrace]
  refine ⟨3623099804622694534798973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9661599478993852092797261 3623099804622694534798973)
  ·
    refine ⟨1358662426733510450549615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3623099804622694534798973 1358662426733510450549615)
    ·
      refine ⟨2037993640100265675824423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1358662426733510450549615 2037993640100265675824423)
      ·
        refine ⟨3056990460150398513736635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2037993640100265675824423 3056990460150398513736635)
        ·
          refine ⟨4585485690225597770604953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3056990460150398513736635 4585485690225597770604953)
          ·
            refine ⟨3439114267669198327953715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4585485690225597770604953 3439114267669198327953715)
            ·
              refine ⟨5158671401503797491930573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3439114267669198327953715 5158671401503797491930573)
              ·
                refine ⟨1934501775563924059473965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5158671401503797491930573 1934501775563924059473965)
                ·
                  refine ⟨725438165836471522302737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1934501775563924059473965 725438165836471522302737)
                  ·
                    refine ⟨544078624377353641727053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 725438165836471522302737 544078624377353641727053)
                    ·
                      refine ⟨204029484141507615647645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 544078624377353641727053 204029484141507615647645)
                      ·
                        rfl

theorem cell23_397346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_397346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397346 prefixEnd_397346 := by exact prefixLift 397346
  have htrace : WordTrace (prefixWord ++ tailWord_397346) baseStart_397346 baseEnd_397346 := by
    simpa [prefixWord, tailWord_397346, baseEnd_397346] using wordTrace_append hprefix tailTrace_397346
  have hstable : (prefixWord ++ tailWord_397346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397346).length < 2 ^ (prefixWord ++ tailWord_397346).sum := by decide
  have hdescent : baseEnd_397346 < baseStart_397346 := by decide
  rcases family_descends (prefixWord ++ tailWord_397346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397359 : List Nat := [1, 1, 2, 1, 2, 1, 1, 5, 3, 3, 3]
def baseStart_397359 : Nat := 118140960795 + 397359 * 2 ^ 59
def prefixEnd_397359 : Nat := 4983230072969 + 3 ^ 40 * 397359 * 2
def baseEnd_397359 : Nat := 204036159390016064785085

theorem tailTrace_397359 : CollatzResearch.WordTrace tailWord_397359 prefixEnd_397359 204036159390016064785085 := by
  unfold tailWord_397359
  simp only [CollatzResearch.WordTrace]
  refine ⟨14492873367443681359419131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9661915578295787572946087 14492873367443681359419131)
  ·
    refine ⟨21739310051165522039128697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14492873367443681359419131 21739310051165522039128697)
    ·
      refine ⟨16304482538374141529346523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21739310051165522039128697 16304482538374141529346523)
      ·
        refine ⟨24456723807561212294019785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16304482538374141529346523 24456723807561212294019785)
        ·
          refine ⟨18342542855670909220514839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24456723807561212294019785 18342542855670909220514839)
          ·
            refine ⟨27513814283506363830772259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18342542855670909220514839 27513814283506363830772259)
            ·
              refine ⟨41270721425259545746158389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27513814283506363830772259 41270721425259545746158389)
              ·
                refine ⟨3869130133618082413702349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41270721425259545746158389 3869130133618082413702349)
                ·
                  refine ⟨1450923800106780905138381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3869130133618082413702349 1450923800106780905138381)
                  ·
                    refine ⟨544096425040042839426893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1450923800106780905138381 544096425040042839426893)
                    ·
                      refine ⟨204036159390016064785085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 544096425040042839426893 204036159390016064785085)
                      ·
                        rfl

theorem cell23_397359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 3, 3].length) (baseStart_397359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397359 prefixEnd_397359 := by exact prefixLift 397359
  have htrace : WordTrace (prefixWord ++ tailWord_397359) baseStart_397359 baseEnd_397359 := by
    simpa [prefixWord, tailWord_397359, baseEnd_397359] using wordTrace_append hprefix tailTrace_397359
  have hstable : (prefixWord ++ tailWord_397359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397359).length < 2 ^ (prefixWord ++ tailWord_397359).sum := by decide
  have hdescent : baseEnd_397359 < baseStart_397359 := by decide
  rcases family_descends (prefixWord ++ tailWord_397359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397360 : List Nat := [2, 1, 1, 1, 2, 5, 1, 5, 1, 2, 2]
def baseStart_397360 : Nat := 118140960795 + 397360 * 2 ^ 59
def prefixEnd_397360 : Nat := 4983230072969 + 3 ^ 40 * 397360 * 2
def baseEnd_397360 : Nat := 204036672870670560872581

theorem tailTrace_397360 : CollatzResearch.WordTrace tailWord_397360 prefixEnd_397360 204036672870670560872581 := by
  unfold tailWord_397360
  simp only [CollatzResearch.WordTrace]
  refine ⟨7246454920220029265102767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9661939893626705686803689 7246454920220029265102767)
  ·
    refine ⟨10869682380330043897654151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7246454920220029265102767 10869682380330043897654151)
    ·
      refine ⟨16304523570495065846481227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10869682380330043897654151 16304523570495065846481227)
      ·
        refine ⟨24456785355742598769721841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16304523570495065846481227 24456785355742598769721841)
        ·
          refine ⟨18342589016806949077291381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24456785355742598769721841 18342589016806949077291381)
          ·
            refine ⟨1719617720325651475996067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18342589016806949077291381 1719617720325651475996067)
            ·
              refine ⟨2579426580488477213994101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1719617720325651475996067 2579426580488477213994101)
              ·
                refine ⟨241821241920794738811947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2579426580488477213994101 241821241920794738811947)
                ·
                  refine ⟨362731862881192108217921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 241821241920794738811947 362731862881192108217921)
                  ·
                    refine ⟨272048897160894081163441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 362731862881192108217921 272048897160894081163441)
                    ·
                      refine ⟨204036672870670560872581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 272048897160894081163441 204036672870670560872581)
                      ·
                        rfl

theorem cell23_397360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 5, 1, 2, 2].length) (baseStart_397360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397360 prefixEnd_397360 := by exact prefixLift 397360
  have htrace : WordTrace (prefixWord ++ tailWord_397360) baseStart_397360 baseEnd_397360 := by
    simpa [prefixWord, tailWord_397360, baseEnd_397360] using wordTrace_append hprefix tailTrace_397360
  have hstable : (prefixWord ++ tailWord_397360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397360).length < 2 ^ (prefixWord ++ tailWord_397360).sum := by decide
  have hdescent : baseEnd_397360 < baseStart_397360 := by decide
  rcases family_descends (prefixWord ++ tailWord_397360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397363 : List Nat := [1, 1, 1, 2, 4, 1, 6, 1, 1, 2, 3]
def baseStart_397363 : Nat := 118140960795 + 397363 * 2 ^ 59
def prefixEnd_397363 : Nat := 4983230072969 + 3 ^ 40 * 397363 * 2
def baseEnd_397363 : Nat := 204038213312634049135067

theorem tailTrace_397363 : CollatzResearch.WordTrace tailWord_397363 prefixEnd_397363 204038213312634049135067 := by
  unfold tailWord_397363
  simp only [CollatzResearch.WordTrace]
  refine ⟨14493019259429190042564743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9662012839619460028376495 14493019259429190042564743)
  ·
    refine ⟨21739528889143785063847115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14493019259429190042564743 21739528889143785063847115)
    ·
      refine ⟨32609293333715677595770673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21739528889143785063847115 32609293333715677595770673)
      ·
        refine ⟨24456970000286758196828005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32609293333715677595770673 24456970000286758196828005)
        ·
          refine ⟨4585681875053767161905251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24456970000286758196828005 4585681875053767161905251)
          ·
            refine ⟨6878522812580650742857877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4585681875053767161905251 6878522812580650742857877)
            ·
              refine ⟨322430756839718003571463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6878522812580650742857877 322430756839718003571463)
              ·
                refine ⟨483646135259577005357195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322430756839718003571463 483646135259577005357195)
                ·
                  refine ⟨725469202889365508035793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 483646135259577005357195 725469202889365508035793)
                  ·
                    refine ⟨544101902167024131026845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 725469202889365508035793 544101902167024131026845)
                    ·
                      refine ⟨204038213312634049135067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 544101902167024131026845 204038213312634049135067)
                      ·
                        rfl

theorem cell23_397363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 1, 1, 2, 3].length) (baseStart_397363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397363 prefixEnd_397363 := by exact prefixLift 397363
  have htrace : WordTrace (prefixWord ++ tailWord_397363) baseStart_397363 baseEnd_397363 := by
    simpa [prefixWord, tailWord_397363, baseEnd_397363] using wordTrace_append hprefix tailTrace_397363
  have hstable : (prefixWord ++ tailWord_397363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397363).length < 2 ^ (prefixWord ++ tailWord_397363).sum := by decide
  have hdescent : baseEnd_397363 < baseStart_397363 := by decide
  rcases family_descends (prefixWord ++ tailWord_397363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397377 : List Nat := [1, 2, 5, 1, 2, 1, 2, 4, 1, 2, 2]
def baseStart_397377 : Nat := 118140960795 + 397377 * 2 ^ 59
def prefixEnd_397377 : Nat := 4983230072969 + 3 ^ 40 * 397377 * 2
def baseEnd_397377 : Nat := 204045402041796994360003

theorem tailTrace_397377 : CollatzResearch.WordTrace tailWord_397377 prefixEnd_397377 204045402041796994360003 := by
  unfold tailWord_397377
  simp only [CollatzResearch.WordTrace]
  refine ⟨14493529881378470433574385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9662353254252313622382923 14493529881378470433574385)
  ·
    refine ⟨10870147411033852825180789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14493529881378470433574385 10870147411033852825180789)
    ·
      refine ⟨1019076319784423702360699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10870147411033852825180789 1019076319784423702360699)
      ·
        refine ⟨1528614479676635553541049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1019076319784423702360699 1528614479676635553541049)
        ·
          refine ⟨1146460859757476665155787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1528614479676635553541049 1146460859757476665155787)
          ·
            refine ⟨1719691289636214997733681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1146460859757476665155787 1719691289636214997733681)
            ·
              refine ⟨1289768467227161248300261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1719691289636214997733681 1289768467227161248300261)
              ·
                refine ⟨241831587605092734056299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1289768467227161248300261 241831587605092734056299)
                ·
                  refine ⟨362747381407639101084449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 241831587605092734056299 362747381407639101084449)
                  ·
                    refine ⟨272060536055729325813337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 362747381407639101084449 272060536055729325813337)
                    ·
                      refine ⟨204045402041796994360003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 272060536055729325813337 204045402041796994360003)
                      ·
                        rfl

theorem cell23_397377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_397377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397377 prefixEnd_397377 := by exact prefixLift 397377
  have htrace : WordTrace (prefixWord ++ tailWord_397377) baseStart_397377 baseEnd_397377 := by
    simpa [prefixWord, tailWord_397377, baseEnd_397377] using wordTrace_append hprefix tailTrace_397377
  have hstable : (prefixWord ++ tailWord_397377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397377).length < 2 ^ (prefixWord ++ tailWord_397377).sum := by decide
  have hdescent : baseEnd_397377 < baseStart_397377 := by decide
  rcases family_descends (prefixWord ++ tailWord_397377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397399 : List Nat := [1, 1, 3, 2, 2, 1, 2, 2, 2, 3, 4]
def baseStart_397399 : Nat := 118140960795 + 397399 * 2 ^ 59
def prefixEnd_397399 : Nat := 4983230072969 + 3 ^ 40 * 397399 * 2
def baseEnd_397399 : Nat := 204056698616195908284901

theorem tailTrace_397399 : CollatzResearch.WordTrace tailWord_397399 prefixEnd_397399 204056698616195908284901 := by
  unfold tailWord_397399
  simp only [CollatzResearch.WordTrace]
  refine ⟨14494332287298768190875251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9662888191532512127250167 14494332287298768190875251)
  ·
    refine ⟨21741498430948152286312877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14494332287298768190875251 21741498430948152286312877)
    ·
      refine ⟨8153061911605557107367329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21741498430948152286312877 8153061911605557107367329)
      ·
        refine ⟨6114796433704167830525497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8153061911605557107367329 6114796433704167830525497)
        ·
          refine ⟨4586097325278125872894123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6114796433704167830525497 4586097325278125872894123)
          ·
            refine ⟨6879145987917188809341185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4586097325278125872894123 6879145987917188809341185)
            ·
              refine ⟨5159359490937891607005889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6879145987917188809341185 5159359490937891607005889)
              ·
                refine ⟨3869519618203418705254417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5159359490937891607005889 3869519618203418705254417)
                ·
                  refine ⟨2902139713652564028940813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3869519618203418705254417 2902139713652564028940813)
                  ·
                    refine ⟨1088302392619711510852805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2902139713652564028940813 1088302392619711510852805)
                    ·
                      refine ⟨204056698616195908284901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1088302392619711510852805 204056698616195908284901)
                      ·
                        rfl

theorem cell23_397399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_397399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397399 prefixEnd_397399 := by exact prefixLift 397399
  have htrace : WordTrace (prefixWord ++ tailWord_397399) baseStart_397399 baseEnd_397399 := by
    simpa [prefixWord, tailWord_397399, baseEnd_397399] using wordTrace_append hprefix tailTrace_397399
  have hstable : (prefixWord ++ tailWord_397399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397399).length < 2 ^ (prefixWord ++ tailWord_397399).sum := by decide
  have hdescent : baseEnd_397399 < baseStart_397399 := by decide
  rcases family_descends (prefixWord ++ tailWord_397399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397454 : List Nat := [4, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2]
def baseStart_397454 : Nat := 118140960795 + 397454 * 2 ^ 59
def prefixEnd_397454 : Nat := 4983230072969 + 3 ^ 40 * 397454 * 2
def baseEnd_397454 : Nat := 204084940052193193097149

theorem tailTrace_397454 : CollatzResearch.WordTrace tailWord_397454 prefixEnd_397454 204084940052193193097149 := by
  unfold tailWord_397454
  simp only [CollatzResearch.WordTrace]
  refine ⟨1812042287762439073015927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9664225534733008389418277 1812042287762439073015927)
  ·
    refine ⟨2718063431643658609523891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1812042287762439073015927 2718063431643658609523891)
    ·
      refine ⟨4077095147465487914285837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2718063431643658609523891 4077095147465487914285837)
      ·
        refine ⟨1528910680299557967857189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4077095147465487914285837 1528910680299557967857189)
        ·
          refine ⟨286670752556167118973223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1528910680299557967857189 286670752556167118973223)
          ·
            refine ⟨430006128834250678459835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286670752556167118973223 430006128834250678459835)
            ·
              refine ⟨645009193251376017689753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 430006128834250678459835 645009193251376017689753)
              ·
                refine ⟨483756894938532013267315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 645009193251376017689753 483756894938532013267315)
                ·
                  refine ⟨725635342407798019900973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 483756894938532013267315 725635342407798019900973)
                  ·
                    refine ⟨272113253402924257462865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 725635342407798019900973 272113253402924257462865)
                    ·
                      refine ⟨204084940052193193097149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 272113253402924257462865 204084940052193193097149)
                      ·
                        rfl

theorem cell23_397454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_397454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397454 prefixEnd_397454 := by exact prefixLift 397454
  have htrace : WordTrace (prefixWord ++ tailWord_397454) baseStart_397454 baseEnd_397454 := by
    simpa [prefixWord, tailWord_397454, baseEnd_397454] using wordTrace_append hprefix tailTrace_397454
  have hstable : (prefixWord ++ tailWord_397454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397454).length < 2 ^ (prefixWord ++ tailWord_397454).sum := by decide
  have hdescent : baseEnd_397454 < baseStart_397454 := by decide
  rcases family_descends (prefixWord ++ tailWord_397454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397546 : List Nat := [3, 1, 3, 1, 1, 2, 3, 1, 8]
def baseStart_397546 : Nat := 118140960795 + 397546 * 2 ^ 59
def prefixEnd_397546 : Nat := 4983230072969 + 3 ^ 40 * 397546 * 2
def baseEnd_397546 : Nat := 22681353363600759238525

theorem tailTrace_397546 : CollatzResearch.WordTrace tailWord_397546 prefixEnd_397546 22681353363600759238525 := by
  unfold tailWord_397546
  simp only [CollatzResearch.WordTrace]
  refine ⟨3624923454441553074119123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9666462545177474864317661 3624923454441553074119123)
  ·
    refine ⟨5437385181662329611178685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3624923454441553074119123 5437385181662329611178685)
    ·
      refine ⟨2039019443123373604192007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5437385181662329611178685 2039019443123373604192007)
      ·
        refine ⟨3058529164685060406288011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2039019443123373604192007 3058529164685060406288011)
        ·
          refine ⟨4587793747027590609432017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3058529164685060406288011 4587793747027590609432017)
          ·
            refine ⟨3440845310270692957074013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4587793747027590609432017 3440845310270692957074013)
            ·
              refine ⟨1290316991351509858902755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3440845310270692957074013 1290316991351509858902755)
              ·
                refine ⟨1935475487027264788354133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1290316991351509858902755 1935475487027264788354133)
                ·
                  refine ⟨22681353363600759238525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1935475487027264788354133 22681353363600759238525)
                  ·
                    rfl

theorem cell23_397546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 8].length) (baseStart_397546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397546 prefixEnd_397546 := by exact prefixLift 397546
  have htrace : WordTrace (prefixWord ++ tailWord_397546) baseStart_397546 baseEnd_397546 := by
    simpa [prefixWord, tailWord_397546, baseEnd_397546] using wordTrace_append hprefix tailTrace_397546
  have hstable : (prefixWord ++ tailWord_397546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397546).length < 2 ^ (prefixWord ++ tailWord_397546).sum := by decide
  have hdescent : baseEnd_397546 < baseStart_397546 := by decide
  rcases family_descends (prefixWord ++ tailWord_397546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397573 : List Nat := [1, 3, 1, 1, 2, 1, 2, 3, 5, 1, 3]
def baseStart_397573 : Nat := 118140960795 + 397573 * 2 ^ 59
def prefixEnd_397573 : Nat := 4983230072969 + 3 ^ 40 * 397573 * 2
def baseEnd_397573 : Nat := 204146044250078227509101

theorem tailTrace_397573 : CollatzResearch.WordTrace tailWord_397573 prefixEnd_397573 204146044250078227509101 := by
  unfold tailWord_397573
  simp only [CollatzResearch.WordTrace]
  refine ⟨14500678588668395907709373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9667119059112263938472915 14500678588668395907709373)
  ·
    refine ⟨5437754470750648465391015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14500678588668395907709373 5437754470750648465391015)
    ·
      refine ⟨8156631706125972698086523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5437754470750648465391015 8156631706125972698086523)
      ·
        refine ⟨12234947559188959047129785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8156631706125972698086523 12234947559188959047129785)
        ·
          refine ⟨9176210669391719285347339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12234947559188959047129785 9176210669391719285347339)
          ·
            refine ⟨13764316004087578928021009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9176210669391719285347339 13764316004087578928021009)
            ·
              refine ⟨10323237003065684196015757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13764316004087578928021009 10323237003065684196015757)
              ·
                refine ⟨3871213876149631573505909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10323237003065684196015757 3871213876149631573505909)
                ·
                  refine ⟨362926300889027960016179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3871213876149631573505909 362926300889027960016179)
                  ·
                    refine ⟨544389451333541940024269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 362926300889027960016179 544389451333541940024269)
                    ·
                      refine ⟨204146044250078227509101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 544389451333541940024269 204146044250078227509101)
                      ·
                        rfl

theorem cell23_397573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 5, 1, 3].length) (baseStart_397573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397573 prefixEnd_397573 := by exact prefixLift 397573
  have htrace : WordTrace (prefixWord ++ tailWord_397573) baseStart_397573 baseEnd_397573 := by
    simpa [prefixWord, tailWord_397573, baseEnd_397573] using wordTrace_append hprefix tailTrace_397573
  have hstable : (prefixWord ++ tailWord_397573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397573).length < 2 ^ (prefixWord ++ tailWord_397573).sum := by decide
  have hdescent : baseEnd_397573 < baseStart_397573 := by decide
  rcases family_descends (prefixWord ++ tailWord_397573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397583 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 6, 3, 2]
def baseStart_397583 : Nat := 118140960795 + 397583 * 2 ^ 59
def prefixEnd_397583 : Nat := 4983230072969 + 3 ^ 40 * 397583 * 2
def baseEnd_397583 : Nat := 204151179056623188384055

theorem tailTrace_397583 : CollatzResearch.WordTrace tailWord_397583 prefixEnd_397583 204151179056623188384055 := by
  unfold tailWord_397583
  simp only [CollatzResearch.WordTrace]
  refine ⟨14501043318632167615573403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9667362212421445077048935 14501043318632167615573403)
  ·
    refine ⟨21751564977948251423360105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14501043318632167615573403 21751564977948251423360105)
    ·
      refine ⟨16313673733461188567520079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21751564977948251423360105 16313673733461188567520079)
      ·
        refine ⟨24470510600191782851280119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16313673733461188567520079 24470510600191782851280119)
        ·
          refine ⟨36705765900287674276920179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24470510600191782851280119 36705765900287674276920179)
          ·
            refine ⟨55058648850431511415380269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36705765900287674276920179 55058648850431511415380269)
            ·
              refine ⟨20646993318911816780767601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55058648850431511415380269 20646993318911816780767601)
              ·
                refine ⟨15485244989183862585575701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20646993318911816780767601 15485244989183862585575701)
                ·
                  refine ⟨725870858867993558698861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15485244989183862585575701 725870858867993558698861)
                  ·
                    refine ⟨272201572075497584512073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 725870858867993558698861 272201572075497584512073)
                    ·
                      refine ⟨204151179056623188384055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 272201572075497584512073 204151179056623188384055)
                      ·
                        rfl

theorem cell23_397583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6, 3, 2].length) (baseStart_397583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397583 prefixEnd_397583 := by exact prefixLift 397583
  have htrace : WordTrace (prefixWord ++ tailWord_397583) baseStart_397583 baseEnd_397583 := by
    simpa [prefixWord, tailWord_397583, baseEnd_397583] using wordTrace_append hprefix tailTrace_397583
  have hstable : (prefixWord ++ tailWord_397583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397583).length < 2 ^ (prefixWord ++ tailWord_397583).sum := by decide
  have hdescent : baseEnd_397583 < baseStart_397583 := by decide
  rcases family_descends (prefixWord ++ tailWord_397583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397600 : List Nat := [2, 1, 1, 5, 2, 1, 1, 1, 4, 3, 2]
def baseStart_397600 : Nat := 118140960795 + 397600 * 2 ^ 59
def prefixEnd_397600 : Nat := 4983230072969 + 3 ^ 40 * 397600 * 2
def baseEnd_397600 : Nat := 204159908227749621871477

theorem tailTrace_397600 : CollatzResearch.WordTrace tailWord_397600 prefixEnd_397600 204159908227749621871477 := by
  unfold tailWord_397600
  simp only [CollatzResearch.WordTrace]
  refine ⟨7250831679785289759471127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9667775573047053012628169 7250831679785289759471127)
  ·
    refine ⟨10876247519677934639206691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7250831679785289759471127 10876247519677934639206691)
    ·
      refine ⟨16314371279516901958810037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10876247519677934639206691 16314371279516901958810037)
      ·
        refine ⟨1529472307454709558638441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16314371279516901958810037 1529472307454709558638441)
        ·
          refine ⟨1147104230591032168978831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1529472307454709558638441 1147104230591032168978831)
          ·
            refine ⟨1720656345886548253468247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1147104230591032168978831 1720656345886548253468247)
            ·
              refine ⟨2580984518829822380202371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1720656345886548253468247 2580984518829822380202371)
              ·
                refine ⟨3871476778244733570303557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2580984518829822380202371 3871476778244733570303557)
                ·
                  refine ⟨725901895920887544431917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3871476778244733570303557 725901895920887544431917)
                  ·
                    refine ⟨272213210970332829161969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 725901895920887544431917 272213210970332829161969)
                    ·
                      refine ⟨204159908227749621871477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 272213210970332829161969 204159908227749621871477)
                      ·
                        rfl

theorem cell23_397600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_397600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397600 prefixEnd_397600 := by exact prefixLift 397600
  have htrace : WordTrace (prefixWord ++ tailWord_397600) baseStart_397600 baseEnd_397600 := by
    simpa [prefixWord, tailWord_397600, baseEnd_397600] using wordTrace_append hprefix tailTrace_397600
  have hstable : (prefixWord ++ tailWord_397600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397600).length < 2 ^ (prefixWord ++ tailWord_397600).sum := by decide
  have hdescent : baseEnd_397600 < baseStart_397600 := by decide
  rcases family_descends (prefixWord ++ tailWord_397600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397614 : List Nat := [4, 1, 3, 3, 1, 2, 2, 1, 6]
def baseStart_397614 : Nat := 118140960795 + 397614 * 2 ^ 59
def prefixEnd_397614 : Nat := 4983230072969 + 3 ^ 40 * 397614 * 2
def baseEnd_397614 : Nat := 22685232995212507455157

theorem tailTrace_397614 : CollatzResearch.WordTrace tailWord_397614 prefixEnd_397614 22685232995212507455157 := by
  unfold tailWord_397614
  simp only [CollatzResearch.WordTrace]
  refine ⟨1812771747689982488743987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9668115987679906606634597 1812771747689982488743987)
  ·
    refine ⟨2719157621534973733115981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1812771747689982488743987 2719157621534973733115981)
    ·
      refine ⟨1019684108075615149918493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2719157621534973733115981 1019684108075615149918493)
      ·
        refine ⟨382381540528355681219435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1019684108075615149918493 382381540528355681219435)
        ·
          refine ⟨573572310792533521829153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382381540528355681219435 573572310792533521829153)
          ·
            refine ⟨430179233094400141371865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 573572310792533521829153 430179233094400141371865)
            ·
              refine ⟨322634424820800106028899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 430179233094400141371865 322634424820800106028899)
              ·
                refine ⟨483951637231200159043349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322634424820800106028899 483951637231200159043349)
                ·
                  refine ⟨22685232995212507455157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 483951637231200159043349 22685232995212507455157)
                  ·
                    rfl

theorem cell23_397614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 1, 6].length) (baseStart_397614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397614 prefixEnd_397614 := by exact prefixLift 397614
  have htrace : WordTrace (prefixWord ++ tailWord_397614) baseStart_397614 baseEnd_397614 := by
    simpa [prefixWord, tailWord_397614, baseEnd_397614] using wordTrace_append hprefix tailTrace_397614
  have hstable : (prefixWord ++ tailWord_397614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397614).length < 2 ^ (prefixWord ++ tailWord_397614).sum := by decide
  have hdescent : baseEnd_397614 < baseStart_397614 := by decide
  rcases family_descends (prefixWord ++ tailWord_397614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397616 : List Nat := [2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 5]
def baseStart_397616 : Nat := 118140960795 + 397616 * 2 ^ 59
def prefixEnd_397616 : Nat := 4983230072969 + 3 ^ 40 * 397616 * 2
def baseEnd_397616 : Nat := 204168123918221559271403

theorem tailTrace_397616 : CollatzResearch.WordTrace tailWord_397616 prefixEnd_397616 204168123918221559271403 := by
  unfold tailWord_397616
  simp only [CollatzResearch.WordTrace]
  refine ⟨7251123463756307125762351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9668164618341742834349801 7251123463756307125762351)
  ·
    refine ⟨10876685195634460688643527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7251123463756307125762351 10876685195634460688643527)
    ·
      refine ⟨16315027793451691032965291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10876685195634460688643527 16315027793451691032965291)
      ·
        refine ⟨24472541690177536549447937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16315027793451691032965291 24472541690177536549447937)
        ·
          refine ⟨18354406267633152412085953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24472541690177536549447937 18354406267633152412085953)
          ·
            refine ⟨13765804700724864309064465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18354406267633152412085953 13765804700724864309064465)
            ·
              refine ⟨10324353525543648231798349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13765804700724864309064465 10324353525543648231798349)
              ·
                refine ⟨3871632572078868086924381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10324353525543648231798349 3871632572078868086924381)
                ·
                  refine ⟨1451862214529575532596643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3871632572078868086924381 1451862214529575532596643)
                  ·
                    refine ⟨2177793321794363298894965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1451862214529575532596643 2177793321794363298894965)
                    ·
                      refine ⟨204168123918221559271403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2177793321794363298894965 204168123918221559271403)
                      ·
                        rfl

theorem cell23_397616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 5].length) (baseStart_397616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397616 prefixEnd_397616 := by exact prefixLift 397616
  have htrace : WordTrace (prefixWord ++ tailWord_397616) baseStart_397616 baseEnd_397616 := by
    simpa [prefixWord, tailWord_397616, baseEnd_397616] using wordTrace_append hprefix tailTrace_397616
  have hstable : (prefixWord ++ tailWord_397616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397616).length < 2 ^ (prefixWord ++ tailWord_397616).sum := by decide
  have hdescent : baseEnd_397616 < baseStart_397616 := by decide
  rcases family_descends (prefixWord ++ tailWord_397616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397630 : List Nat := [4, 2, 1, 2, 1, 3, 1, 1, 3, 1, 4]
def baseStart_397630 : Nat := 118140960795 + 397630 * 2 ^ 59
def prefixEnd_397630 : Nat := 4983230072969 + 3 ^ 40 * 397630 * 2
def baseEnd_397630 : Nat := 204175312647384504496339

theorem tailTrace_397630 : CollatzResearch.WordTrace tailWord_397630 prefixEnd_397630 204175312647384504496339 := by
  unfold tailWord_397630
  simp only [CollatzResearch.WordTrace]
  refine ⟨1812844693682736830316793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9668505032974596428356229 1812844693682736830316793)
  ·
    refine ⟨1359633520262052622737595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1812844693682736830316793 1359633520262052622737595)
    ·
      refine ⟨2039450280393078934106393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1359633520262052622737595 2039450280393078934106393)
      ·
        refine ⟨1529587710294809200579795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2039450280393078934106393 1529587710294809200579795)
        ·
          refine ⟨2294381565442213800869693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1529587710294809200579795 2294381565442213800869693)
          ·
            refine ⟨860393087040830175326135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2294381565442213800869693 860393087040830175326135)
            ·
              refine ⟨1290589630561245262989203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 860393087040830175326135 1290589630561245262989203)
              ·
                refine ⟨1935884445841867894483805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1290589630561245262989203 1935884445841867894483805)
                ·
                  refine ⟨725956667190700460431427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1935884445841867894483805 725956667190700460431427)
                  ·
                    refine ⟨1088935000786050690647141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 725956667190700460431427 1088935000786050690647141)
                    ·
                      refine ⟨204175312647384504496339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1088935000786050690647141 204175312647384504496339)
                      ·
                        rfl

theorem cell23_397630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_397630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397630 prefixEnd_397630 := by exact prefixLift 397630
  have htrace : WordTrace (prefixWord ++ tailWord_397630) baseStart_397630 baseEnd_397630 := by
    simpa [prefixWord, tailWord_397630, baseEnd_397630] using wordTrace_append hprefix tailTrace_397630
  have hstable : (prefixWord ++ tailWord_397630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397630).length < 2 ^ (prefixWord ++ tailWord_397630).sum := by decide
  have hdescent : baseEnd_397630 < baseStart_397630 := by decide
  rcases family_descends (prefixWord ++ tailWord_397630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397650 : List Nat := [3, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3]
def baseStart_397650 : Nat := 118140960795 + 397650 * 2 ^ 59
def prefixEnd_397650 : Nat := 4983230072969 + 3 ^ 40 * 397650 * 2
def baseEnd_397650 : Nat := 204185582260474426246247

theorem tailTrace_397650 : CollatzResearch.WordTrace tailWord_397650 prefixEnd_397650 204185582260474426246247 := by
  unfold tailWord_397650
  simp only [CollatzResearch.WordTrace]
  refine ⟨3625871752347359514565601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9668991339592958705508269 3625871752347359514565601)
  ·
    refine ⟨2719403814260519635924201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3625871752347359514565601 2719403814260519635924201)
    ·
      refine ⟨2039552860695389726943151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2719403814260519635924201 2039552860695389726943151)
      ·
        refine ⟨3059329291043084590414727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2039552860695389726943151 3059329291043084590414727)
        ·
          refine ⟨4588993936564626885622091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3059329291043084590414727 4588993936564626885622091)
          ·
            refine ⟨6883490904846940328433137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4588993936564626885622091 6883490904846940328433137)
            ·
              refine ⟨5162618178635205246324853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6883490904846940328433137 5162618178635205246324853)
              ·
                refine ⟨483995454247050491842955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5162618178635205246324853 483995454247050491842955)
                ·
                  refine ⟨725993181370575737764433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 483995454247050491842955 725993181370575737764433)
                  ·
                    refine ⟨544494886027931803323325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 725993181370575737764433 544494886027931803323325)
                    ·
                      refine ⟨204185582260474426246247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 544494886027931803323325 204185582260474426246247)
                      ·
                        rfl

theorem cell23_397650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_397650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397650 prefixEnd_397650 := by exact prefixLift 397650
  have htrace : WordTrace (prefixWord ++ tailWord_397650) baseStart_397650 baseEnd_397650 := by
    simpa [prefixWord, tailWord_397650, baseEnd_397650] using wordTrace_append hprefix tailTrace_397650
  have hstable : (prefixWord ++ tailWord_397650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397650).length < 2 ^ (prefixWord ++ tailWord_397650).sum := by decide
  have hdescent : baseEnd_397650 < baseStart_397650 := by decide
  rcases family_descends (prefixWord ++ tailWord_397650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397653 : List Nat := [1, 3, 2, 2, 5, 10]
def baseStart_397653 : Nat := 118140960795 + 397653 * 2 ^ 59
def prefixEnd_397653 : Nat := 4983230072969 + 3 ^ 40 * 397653 * 2
def baseEnd_397653 : Nat := 840276225112913228431

theorem tailTrace_397653 : CollatzResearch.WordTrace tailWord_397653 prefixEnd_397653 840276225112913228431 := by
  unfold tailWord_397653
  simp only [CollatzResearch.WordTrace]
  refine ⟨14503596428378569570621613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9669064285585713047081075 14503596428378569570621613)
  ·
    refine ⟨5438848660641963588983105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14503596428378569570621613 5438848660641963588983105)
    ·
      refine ⟨4079136495481472691737329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5438848660641963588983105 4079136495481472691737329)
      ·
        refine ⟨3059352371611104518802997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4079136495481472691737329 3059352371611104518802997)
        ·
          refine ⟨286814284838541048637781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3059352371611104518802997 286814284838541048637781)
          ·
            refine ⟨840276225112913228431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 286814284838541048637781 840276225112913228431)
            ·
              rfl

theorem cell23_397653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 10].length) (baseStart_397653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397653 prefixEnd_397653 := by exact prefixLift 397653
  have htrace : WordTrace (prefixWord ++ tailWord_397653) baseStart_397653 baseEnd_397653 := by
    simpa [prefixWord, tailWord_397653, baseEnd_397653] using wordTrace_append hprefix tailTrace_397653
  have hstable : (prefixWord ++ tailWord_397653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397653).length < 2 ^ (prefixWord ++ tailWord_397653).sum := by decide
  have hdescent : baseEnd_397653 < baseStart_397653 := by decide
  rcases family_descends (prefixWord ++ tailWord_397653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397656 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 2, 2, 6]
def baseStart_397656 : Nat := 118140960795 + 397656 * 2 ^ 59
def prefixEnd_397656 : Nat := 4983230072969 + 3 ^ 40 * 397656 * 2
def baseEnd_397656 : Nat := 204188663144401402771219

theorem tailTrace_397656 : CollatzResearch.WordTrace tailWord_397656 prefixEnd_397656 204188663144401402771219 := by
  unfold tailWord_397656
  simp only [CollatzResearch.WordTrace]
  refine ⟨7251852923683850541490411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9669137231578467388653881 7251852923683850541490411)
  ·
    refine ⟨10877779385525775812235617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7251852923683850541490411 10877779385525775812235617)
    ·
      refine ⟨8158334539144331859176713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10877779385525775812235617 8158334539144331859176713)
      ·
        refine ⟨6118750904358248894382535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8158334539144331859176713 6118750904358248894382535)
        ·
          refine ⟨9178126356537373341573803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6118750904358248894382535 9178126356537373341573803)
          ·
            refine ⟨13767189534806060012360705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9178126356537373341573803 13767189534806060012360705)
            ·
              refine ⟨10325392151104545009270529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13767189534806060012360705 10325392151104545009270529)
              ·
                refine ⟨7744044113328408756952897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10325392151104545009270529 7744044113328408756952897)
                ·
                  refine ⟨5808033084996306567714673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7744044113328408756952897 5808033084996306567714673)
                  ·
                    refine ⟨4356024813747229925786005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5808033084996306567714673 4356024813747229925786005)
                    ·
                      refine ⟨204188663144401402771219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4356024813747229925786005 204188663144401402771219)
                      ·
                        rfl

theorem cell23_397656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_397656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397656 prefixEnd_397656 := by exact prefixLift 397656
  have htrace : WordTrace (prefixWord ++ tailWord_397656) baseStart_397656 baseEnd_397656 := by
    simpa [prefixWord, tailWord_397656, baseEnd_397656] using wordTrace_append hprefix tailTrace_397656
  have hstable : (prefixWord ++ tailWord_397656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397656).length < 2 ^ (prefixWord ++ tailWord_397656).sum := by decide
  have hdescent : baseEnd_397656 < baseStart_397656 := by decide
  rcases family_descends (prefixWord ++ tailWord_397656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397680 : List Nat := [2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 3]
def baseStart_397680 : Nat := 118140960795 + 397680 * 2 ^ 59
def prefixEnd_397680 : Nat := 4983230072969 + 3 ^ 40 * 397680 * 2
def baseEnd_397680 : Nat := 204200986680109308871109

theorem tailTrace_397680 : CollatzResearch.WordTrace tailWord_397680 prefixEnd_397680 204200986680109308871109 := by
  unfold tailWord_397680
  simp only [CollatzResearch.WordTrace]
  refine ⟨7252290599640376590927247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9669720799520502121236329 7252290599640376590927247)
  ·
    refine ⟨10878435899460564886390871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7252290599640376590927247 10878435899460564886390871)
    ·
      refine ⟨16317653849190847329586307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10878435899460564886390871 16317653849190847329586307)
      ·
        refine ⟨24476480773786270994379461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16317653849190847329586307 24476480773786270994379461)
        ·
          refine ⟨4589340145084925811446149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24476480773786270994379461 4589340145084925811446149)
          ·
            refine ⟨860501277203423589646153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4589340145084925811446149 860501277203423589646153)
            ·
              refine ⟨645375957902567692234615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 860501277203423589646153 645375957902567692234615)
              ·
                refine ⟨968063936853851538351923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 645375957902567692234615 968063936853851538351923)
                ·
                  refine ⟨1452095905280777307527885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 968063936853851538351923 1452095905280777307527885)
                  ·
                    refine ⟨544535964480291490322957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1452095905280777307527885 544535964480291490322957)
                    ·
                      refine ⟨204200986680109308871109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 544535964480291490322957 204200986680109308871109)
                      ·
                        rfl

theorem cell23_397680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 3].length) (baseStart_397680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397680 prefixEnd_397680 := by exact prefixLift 397680
  have htrace : WordTrace (prefixWord ++ tailWord_397680) baseStart_397680 baseEnd_397680 := by
    simpa [prefixWord, tailWord_397680, baseEnd_397680] using wordTrace_append hprefix tailTrace_397680
  have hstable : (prefixWord ++ tailWord_397680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397680).length < 2 ^ (prefixWord ++ tailWord_397680).sum := by decide
  have hdescent : baseEnd_397680 < baseStart_397680 := by decide
  rcases family_descends (prefixWord ++ tailWord_397680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397698 : List Nat := [3, 4, 2, 1, 3, 1, 2, 1, 1, 1, 4]
def baseStart_397698 : Nat := 118140960795 + 397698 * 2 ^ 59
def prefixEnd_397698 : Nat := 4983230072969 + 3 ^ 40 * 397698 * 2
def baseEnd_397698 : Nat := 204210229331890238446027

theorem tailTrace_397698 : CollatzResearch.WordTrace tailWord_397698 prefixEnd_397698 204210229331890238446027 := by
  unfold tailWord_397698
  simp only [CollatzResearch.WordTrace]
  refine ⟨3626309428303885564002437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9670158475477028170673165 3626309428303885564002437)
  ·
    refine ⟨679933017806978543250457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3626309428303885564002437 679933017806978543250457)
    ·
      refine ⟨509949763355233907437843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 679933017806978543250457 509949763355233907437843)
      ·
        refine ⟨764924645032850861156765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 509949763355233907437843 764924645032850861156765)
        ·
          refine ⟨286846741887319072933787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 764924645032850861156765 286846741887319072933787)
          ·
            refine ⟨430270112830978609400681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286846741887319072933787 430270112830978609400681)
            ·
              refine ⟨322702584623233957050511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 430270112830978609400681 322702584623233957050511)
              ·
                refine ⟨484053876934850935575767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322702584623233957050511 484053876934850935575767)
                ·
                  refine ⟨726080815402276403363651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 484053876934850935575767 726080815402276403363651)
                  ·
                    refine ⟨1089121223103414605045477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 726080815402276403363651 1089121223103414605045477)
                    ·
                      refine ⟨204210229331890238446027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1089121223103414605045477 204210229331890238446027)
                      ·
                        rfl

theorem cell23_397698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_397698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397698 prefixEnd_397698 := by exact prefixLift 397698
  have htrace : WordTrace (prefixWord ++ tailWord_397698) baseStart_397698 baseEnd_397698 := by
    simpa [prefixWord, tailWord_397698, baseEnd_397698] using wordTrace_append hprefix tailTrace_397698
  have hstable : (prefixWord ++ tailWord_397698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397698).length < 2 ^ (prefixWord ++ tailWord_397698).sum := by decide
  have hdescent : baseEnd_397698 < baseStart_397698 := by decide
  rcases family_descends (prefixWord ++ tailWord_397698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397707 : List Nat := [1, 1, 1, 1, 4, 5, 1, 3, 1, 3, 2]
def baseStart_397707 : Nat := 118140960795 + 397707 * 2 ^ 59
def prefixEnd_397707 : Nat := 4983230072969 + 3 ^ 40 * 397707 * 2
def baseEnd_397707 : Nat := 204214850657780703233485

theorem tailTrace_397707 : CollatzResearch.WordTrace tailWord_397707 prefixEnd_397707 204214850657780703233485 := by
  unfold tailWord_397707
  simp only [CollatzResearch.WordTrace]
  refine ⟨14505565970182936793087375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9670377313455291195391583 14505565970182936793087375)
  ·
    refine ⟨21758348955274405189631063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14505565970182936793087375 21758348955274405189631063)
    ·
      refine ⟨32637523432911607784446595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21758348955274405189631063 32637523432911607784446595)
      ·
        refine ⟨48956285149367411676669893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32637523432911607784446595 48956285149367411676669893)
        ·
          refine ⟨9179303465506389689375605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48956285149367411676669893 9179303465506389689375605)
          ·
            refine ⟨860559699891224033378963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9179303465506389689375605 860559699891224033378963)
            ·
              refine ⟨1290839549836836050068445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 860559699891224033378963 1290839549836836050068445)
              ·
                refine ⟨484064831188813518775667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1290839549836836050068445 484064831188813518775667)
                ·
                  refine ⟨726097246783220278163501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 484064831188813518775667 726097246783220278163501)
                  ·
                    refine ⟨272286467543707604311313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 726097246783220278163501 272286467543707604311313)
                    ·
                      refine ⟨204214850657780703233485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 272286467543707604311313 204214850657780703233485)
                      ·
                        rfl

theorem cell23_397707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3, 1, 3, 2].length) (baseStart_397707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397707 prefixEnd_397707 := by exact prefixLift 397707
  have htrace : WordTrace (prefixWord ++ tailWord_397707) baseStart_397707 baseEnd_397707 := by
    simpa [prefixWord, tailWord_397707, baseEnd_397707] using wordTrace_append hprefix tailTrace_397707
  have hstable : (prefixWord ++ tailWord_397707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397707).length < 2 ^ (prefixWord ++ tailWord_397707).sum := by decide
  have hdescent : baseEnd_397707 < baseStart_397707 := by decide
  rcases family_descends (prefixWord ++ tailWord_397707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397733 : List Nat := [1, 3, 1, 2, 1, 1, 3, 3, 2, 2, 4]
def baseStart_397733 : Nat := 118140960795 + 397733 * 2 ^ 59
def prefixEnd_397733 : Nat := 4983230072969 + 3 ^ 40 * 397733 * 2
def baseEnd_397733 : Nat := 204228201154797601508365

theorem tailTrace_397733 : CollatzResearch.WordTrace tailWord_397733 prefixEnd_397733 204228201154797601508365 := by
  unfold tailWord_397733
  simp only [CollatzResearch.WordTrace]
  refine ⟨14506514268088743233533853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9671009512059162155689235 14506514268088743233533853)
  ·
    refine ⟨5439942850533278712575195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14506514268088743233533853 5439942850533278712575195)
    ·
      refine ⟨8159914275799918068862793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5439942850533278712575195 8159914275799918068862793)
      ·
        refine ⟨6119935706849938551647095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8159914275799918068862793 6119935706849938551647095)
        ·
          refine ⟨9179903560274907827470643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6119935706849938551647095 9179903560274907827470643)
          ·
            refine ⟨13769855340412361741205965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9179903560274907827470643 13769855340412361741205965)
            ·
              refine ⟨5163695752654635652952237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13769855340412361741205965 5163695752654635652952237)
              ·
                refine ⟨1936385907245488369857089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5163695752654635652952237 1936385907245488369857089)
                ·
                  refine ⟨1452289430434116277392817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1936385907245488369857089 1452289430434116277392817)
                  ·
                    refine ⟨1089217072825587208044613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1452289430434116277392817 1089217072825587208044613)
                    ·
                      refine ⟨204228201154797601508365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1089217072825587208044613 204228201154797601508365)
                      ·
                        rfl

theorem cell23_397733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_397733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397733 prefixEnd_397733 := by exact prefixLift 397733
  have htrace : WordTrace (prefixWord ++ tailWord_397733) baseStart_397733 baseEnd_397733 := by
    simpa [prefixWord, tailWord_397733, baseEnd_397733] using wordTrace_append hprefix tailTrace_397733
  have hstable : (prefixWord ++ tailWord_397733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397733).length < 2 ^ (prefixWord ++ tailWord_397733).sum := by decide
  have hdescent : baseEnd_397733 < baseStart_397733 := by decide
  rcases family_descends (prefixWord ++ tailWord_397733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397737 : List Nat := [1, 2, 1, 1, 1, 1, 3, 7, 2, 2, 2]
def baseStart_397737 : Nat := 118140960795 + 397737 * 2 ^ 59
def prefixEnd_397737 : Nat := 4983230072969 + 3 ^ 40 * 397737 * 2
def baseEnd_397737 : Nat := 204230255077415585858347

theorem tailTrace_397737 : CollatzResearch.WordTrace tailWord_397737 prefixEnd_397737 204230255077415585858347 := by
  unfold tailWord_397737
  simp only [CollatzResearch.WordTrace]
  refine ⟨14506660160074251916679465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9671106773382834611119643 14506660160074251916679465)
  ·
    refine ⟨10879995120055688937509599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14506660160074251916679465 10879995120055688937509599)
    ·
      refine ⟨16319992680083533406264399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10879995120055688937509599 16319992680083533406264399)
      ·
        refine ⟨24479989020125300109396599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16319992680083533406264399 24479989020125300109396599)
        ·
          refine ⟨36719983530187950164094899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24479989020125300109396599 36719983530187950164094899)
          ·
            refine ⟨55079975295281925246142349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36719983530187950164094899 55079975295281925246142349)
            ·
              refine ⟨20654990735730721967303381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55079975295281925246142349 20654990735730721967303381)
              ·
                refine ⟨484101345368688796108673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 20654990735730721967303381 484101345368688796108673)
                ·
                  refine ⟨363076009026516597081505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 484101345368688796108673 363076009026516597081505)
                  ·
                    refine ⟨272307006769887447811129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 363076009026516597081505 272307006769887447811129)
                    ·
                      refine ⟨204230255077415585858347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 272307006769887447811129 204230255077415585858347)
                      ·
                        rfl

theorem cell23_397737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7, 2, 2, 2].length) (baseStart_397737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397737 prefixEnd_397737 := by exact prefixLift 397737
  have htrace : WordTrace (prefixWord ++ tailWord_397737) baseStart_397737 baseEnd_397737 := by
    simpa [prefixWord, tailWord_397737, baseEnd_397737] using wordTrace_append hprefix tailTrace_397737
  have hstable : (prefixWord ++ tailWord_397737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397737).length < 2 ^ (prefixWord ++ tailWord_397737).sum := by decide
  have hdescent : baseEnd_397737 < baseStart_397737 := by decide
  rcases family_descends (prefixWord ++ tailWord_397737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397741 : List Nat := [1, 5, 2, 2, 2, 1, 2, 2, 1, 3, 2]
def baseStart_397741 : Nat := 118140960795 + 397741 * 2 ^ 59
def prefixEnd_397741 : Nat := 4983230072969 + 3 ^ 40 * 397741 * 2
def baseEnd_397741 : Nat := 204232309000033570208329

theorem tailTrace_397741 : CollatzResearch.WordTrace tailWord_397741 prefixEnd_397741 204232309000033570208329 := by
  unfold tailWord_397741
  simp only [CollatzResearch.WordTrace]
  refine ⟨14506806052059760599825077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9671204034706507066550051 14506806052059760599825077)
  ·
    refine ⟨1360013067380602556233601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14506806052059760599825077 1360013067380602556233601)
    ·
      refine ⟨1020009800535451917175201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1360013067380602556233601 1020009800535451917175201)
      ·
        refine ⟨765007350401588937881401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1020009800535451917175201 765007350401588937881401)
        ·
          refine ⟨573755512801191703411051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 765007350401588937881401 573755512801191703411051)
          ·
            refine ⟨860633269201787555116577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 573755512801191703411051 860633269201787555116577)
            ·
              refine ⟨645474951901340666337433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 860633269201787555116577 645474951901340666337433)
              ·
                refine ⟨484106213926005499753075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 645474951901340666337433 484106213926005499753075)
                ·
                  refine ⟨726159320889008249629613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 484106213926005499753075 726159320889008249629613)
                  ·
                    refine ⟨272309745333378093611105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 726159320889008249629613 272309745333378093611105)
                    ·
                      refine ⟨204232309000033570208329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 272309745333378093611105 204232309000033570208329)
                      ·
                        rfl

theorem cell23_397741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_397741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397741 prefixEnd_397741 := by exact prefixLift 397741
  have htrace : WordTrace (prefixWord ++ tailWord_397741) baseStart_397741 baseEnd_397741 := by
    simpa [prefixWord, tailWord_397741, baseEnd_397741] using wordTrace_append hprefix tailTrace_397741
  have hstable : (prefixWord ++ tailWord_397741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397741).length < 2 ^ (prefixWord ++ tailWord_397741).sum := by decide
  have hdescent : baseEnd_397741 < baseStart_397741 := by decide
  rcases family_descends (prefixWord ++ tailWord_397741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397823 : List Nat := [1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 6]
def baseStart_397823 : Nat := 118140960795 + 397823 * 2 ^ 59
def prefixEnd_397823 : Nat := 4983230072969 + 3 ^ 40 * 397823 * 2
def baseEnd_397823 : Nat := 204274414413702249382951

theorem tailTrace_397823 : CollatzResearch.WordTrace tailWord_397823 prefixEnd_397823 204274414413702249382951 := by
  unfold tailWord_397823
  simp only [CollatzResearch.WordTrace]
  refine ⟨14509796837762688604310123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9673197891841792402873415 14509796837762688604310123)
  ·
    refine ⟨21764695256644032906465185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14509796837762688604310123 21764695256644032906465185)
    ·
      refine ⟨16323521442483024679848889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21764695256644032906465185 16323521442483024679848889)
      ·
        refine ⟨12242641081862268509886667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16323521442483024679848889 12242641081862268509886667)
        ·
          refine ⟨18363961622793402764830001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12242641081862268509886667 18363961622793402764830001)
          ·
            refine ⟨13772971217095052073622501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18363961622793402764830001 13772971217095052073622501)
            ·
              refine ⟨2582432103205322263804219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13772971217095052073622501 2582432103205322263804219)
              ·
                refine ⟨3873648154807983395706329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2582432103205322263804219 3873648154807983395706329)
                ·
                  refine ⟨2905236116105987546779747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3873648154807983395706329 2905236116105987546779747)
                  ·
                    refine ⟨4357854174158981320169621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2905236116105987546779747 4357854174158981320169621)
                    ·
                      refine ⟨204274414413702249382951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4357854174158981320169621 204274414413702249382951)
                      ·
                        rfl

theorem cell23_397823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_397823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397823 prefixEnd_397823 := by exact prefixLift 397823
  have htrace : WordTrace (prefixWord ++ tailWord_397823) baseStart_397823 baseEnd_397823 := by
    simpa [prefixWord, tailWord_397823, baseEnd_397823] using wordTrace_append hprefix tailTrace_397823
  have hstable : (prefixWord ++ tailWord_397823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397823).length < 2 ^ (prefixWord ++ tailWord_397823).sum := by decide
  have hdescent : baseEnd_397823 < baseStart_397823 := by decide
  rcases family_descends (prefixWord ++ tailWord_397823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397844 : List Nat := [2, 4, 3, 1, 1, 1, 1, 1, 1, 6, 2]
def baseStart_397844 : Nat := 118140960795 + 397844 * 2 ^ 59
def prefixEnd_397844 : Nat := 4983230072969 + 3 ^ 40 * 397844 * 2
def baseEnd_397844 : Nat := 204285197507446667220355

theorem tailTrace_397844 : CollatzResearch.WordTrace tailWord_397844 prefixEnd_397844 204285197507446667220355 := by
  unfold tailWord_397844
  simp only [CollatzResearch.WordTrace]
  refine ⟨7255281385343304595412293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9673708513791072793883057 7255281385343304595412293)
  ·
    refine ⟨1360365259751869611639805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7255281385343304595412293 1360365259751869611639805)
    ·
      refine ⟨510136972406951104364927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1360365259751869611639805 510136972406951104364927)
      ·
        refine ⟨765205458610426656547391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510136972406951104364927 765205458610426656547391)
        ·
          refine ⟨1147808187915639984821087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 765205458610426656547391 1147808187915639984821087)
          ·
            refine ⟨1721712281873459977231631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1147808187915639984821087 1721712281873459977231631)
            ·
              refine ⟨2582568422810189965847447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1721712281873459977231631 2582568422810189965847447)
              ·
                refine ⟨3873852634215284948771171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2582568422810189965847447 3873852634215284948771171)
                ·
                  refine ⟨5810778951322927423156757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3873852634215284948771171 5810778951322927423156757)
                  ·
                    refine ⟨272380263343262222960473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5810778951322927423156757 272380263343262222960473)
                    ·
                      refine ⟨204285197507446667220355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 272380263343262222960473 204285197507446667220355)
                      ·
                        rfl

theorem cell23_397844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_397844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397844 prefixEnd_397844 := by exact prefixLift 397844
  have htrace : WordTrace (prefixWord ++ tailWord_397844) baseStart_397844 baseEnd_397844 := by
    simpa [prefixWord, tailWord_397844, baseEnd_397844] using wordTrace_append hprefix tailTrace_397844
  have hstable : (prefixWord ++ tailWord_397844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397844).length < 2 ^ (prefixWord ++ tailWord_397844).sum := by decide
  have hdescent : baseEnd_397844 < baseStart_397844 := by decide
  rcases family_descends (prefixWord ++ tailWord_397844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397850 : List Nat := [3, 1, 1, 3, 1, 1, 4, 3, 6]
def baseStart_397850 : Nat := 118140960795 + 397850 * 2 ^ 59
def prefixEnd_397850 : Nat := 4983230072969 + 3 ^ 40 * 397850 * 2
def baseEnd_397850 : Nat := 22698697599041515971703

theorem tailTrace_397850 : CollatzResearch.WordTrace tailWord_397850 prefixEnd_397850 22698697599041515971703 := by
  unfold tailWord_397850
  simp only [CollatzResearch.WordTrace]
  refine ⟨3627695402166218053885751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9673854405776581477028669 3627695402166218053885751)
  ·
    refine ⟨5441543103249327080828627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3627695402166218053885751 5441543103249327080828627)
    ·
      refine ⟨8162314654873990621242941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5441543103249327080828627 8162314654873990621242941)
      ·
        refine ⟨3060867995577746482966103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8162314654873990621242941 3060867995577746482966103)
        ·
          refine ⟨4591301993366619724449155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3060867995577746482966103 4591301993366619724449155)
          ·
            refine ⟨6886952990049929586673733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4591301993366619724449155 6886952990049929586673733)
            ·
              refine ⟨1291303685634361797501325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6886952990049929586673733 1291303685634361797501325)
              ·
                refine ⟨484238882112885674062997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1291303685634361797501325 484238882112885674062997)
                ·
                  refine ⟨22698697599041515971703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 484238882112885674062997 22698697599041515971703)
                  ·
                    rfl

theorem cell23_397850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3, 6].length) (baseStart_397850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397850 prefixEnd_397850 := by exact prefixLift 397850
  have htrace : WordTrace (prefixWord ++ tailWord_397850) baseStart_397850 baseEnd_397850 := by
    simpa [prefixWord, tailWord_397850, baseEnd_397850] using wordTrace_append hprefix tailTrace_397850
  have hstable : (prefixWord ++ tailWord_397850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397850).length < 2 ^ (prefixWord ++ tailWord_397850).sum := by decide
  have hdescent : baseEnd_397850 < baseStart_397850 := by decide
  rcases family_descends (prefixWord ++ tailWord_397850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397864 : List Nat := [2, 1, 5, 2, 1, 1, 3, 1, 2, 2, 3]
def baseStart_397864 : Nat := 118140960795 + 397864 * 2 ^ 59
def prefixEnd_397864 : Nat := 4983230072969 + 3 ^ 40 * 397864 * 2
def baseEnd_397864 : Nat := 204295467120536588970263

theorem tailTrace_397864 : CollatzResearch.WordTrace tailWord_397864 prefixEnd_397864 204295467120536588970263 := by
  unfold tailWord_397864
  simp only [CollatzResearch.WordTrace]
  refine ⟨7255646115307076303276323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9674194820409435071035097 7255646115307076303276323)
  ·
    refine ⟨10883469172960614454914485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7255646115307076303276323 10883469172960614454914485)
    ·
      refine ⟨1020325234965057605148233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10883469172960614454914485 1020325234965057605148233)
      ·
        refine ⟨765243926223793203861175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1020325234965057605148233 765243926223793203861175)
        ·
          refine ⟨1147865889335689805791763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 765243926223793203861175 1147865889335689805791763)
          ·
            refine ⟨1721798834003534708687645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1147865889335689805791763 1721798834003534708687645)
            ·
              refine ⟨645674562751325515757867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1721798834003534708687645 645674562751325515757867)
              ·
                refine ⟨968511844126988273636801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 645674562751325515757867 968511844126988273636801)
                ·
                  refine ⟨726383883095241205227601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 968511844126988273636801 726383883095241205227601)
                  ·
                    refine ⟨544787912321430903920701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 726383883095241205227601 544787912321430903920701)
                    ·
                      refine ⟨204295467120536588970263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 544787912321430903920701 204295467120536588970263)
                      ·
                        rfl

theorem cell23_397864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_397864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397864 prefixEnd_397864 := by exact prefixLift 397864
  have htrace : WordTrace (prefixWord ++ tailWord_397864) baseStart_397864 baseEnd_397864 := by
    simpa [prefixWord, tailWord_397864, baseEnd_397864] using wordTrace_append hprefix tailTrace_397864
  have hstable : (prefixWord ++ tailWord_397864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397864).length < 2 ^ (prefixWord ++ tailWord_397864).sum := by decide
  have hdescent : baseEnd_397864 < baseStart_397864 := by decide
  rcases family_descends (prefixWord ++ tailWord_397864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397877 : List Nat := [1, 3, 3, 1, 1, 2, 1, 2, 5, 1, 3]
def baseStart_397877 : Nat := 118140960795 + 397877 * 2 ^ 59
def prefixEnd_397877 : Nat := 4983230072969 + 3 ^ 40 * 397877 * 2
def baseEnd_397877 : Nat := 204302142369045038107703

theorem tailTrace_397877 : CollatzResearch.WordTrace tailWord_397877 prefixEnd_397877 204302142369045038107703 := by
  unfold tailWord_397877
  simp only [CollatzResearch.WordTrace]
  refine ⟨14511766379567055826775885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9674510919711370551183923 14511766379567055826775885)
  ·
    refine ⟨5441912392337645935040957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14511766379567055826775885 5441912392337645935040957)
    ·
      refine ⟨2040717147126617225640359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5441912392337645935040957 2040717147126617225640359)
      ·
        refine ⟨3061075720689925838460539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2040717147126617225640359 3061075720689925838460539)
        ·
          refine ⟨4591613581034888757690809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3061075720689925838460539 4591613581034888757690809)
          ·
            refine ⟨3443710185776166568268107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4591613581034888757690809 3443710185776166568268107)
            ·
              refine ⟨5165565278664249852402161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3443710185776166568268107 5165565278664249852402161)
              ·
                refine ⟨3874173958998187389301621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5165565278664249852402161 3874173958998187389301621)
                ·
                  refine ⟨363203808656080067747027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3874173958998187389301621 363203808656080067747027)
                  ·
                    refine ⟨544805712984120101620541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 363203808656080067747027 544805712984120101620541)
                    ·
                      refine ⟨204302142369045038107703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 544805712984120101620541 204302142369045038107703)
                      ·
                        rfl

theorem cell23_397877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_397877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397877 prefixEnd_397877 := by exact prefixLift 397877
  have htrace : WordTrace (prefixWord ++ tailWord_397877) baseStart_397877 baseEnd_397877 := by
    simpa [prefixWord, tailWord_397877, baseEnd_397877] using wordTrace_append hprefix tailTrace_397877
  have hstable : (prefixWord ++ tailWord_397877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397877).length < 2 ^ (prefixWord ++ tailWord_397877).sum := by decide
  have hdescent : baseEnd_397877 < baseStart_397877 := by decide
  rcases family_descends (prefixWord ++ tailWord_397877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397887 : List Nat := [1, 1, 2, 2, 3, 2, 2, 1, 4, 3, 2]
def baseStart_397887 : Nat := 118140960795 + 397887 * 2 ^ 59
def prefixEnd_397887 : Nat := 4983230072969 + 3 ^ 40 * 397887 * 2
def baseEnd_397887 : Nat := 204307277175589998982657

theorem tailTrace_397887 : CollatzResearch.WordTrace tailWord_397887 prefixEnd_397887 204307277175589998982657 := by
  unfold tailWord_397887
  simp only [CollatzResearch.WordTrace]
  refine ⟨14512131109530827534639915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9674754073020551689759943 14512131109530827534639915)
  ·
    refine ⟨21768196664296241301959873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14512131109530827534639915 21768196664296241301959873)
    ·
      refine ⟨16326147498222180976469905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21768196664296241301959873 16326147498222180976469905)
      ·
        refine ⟨12244610623666635732352429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16326147498222180976469905 12244610623666635732352429)
        ·
          refine ⟨4591728983874988399632161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12244610623666635732352429 4591728983874988399632161)
          ·
            refine ⟨3443796737906241299724121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4591728983874988399632161 3443796737906241299724121)
            ·
              refine ⟨2582847553429680974793091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3443796737906241299724121 2582847553429680974793091)
              ·
                refine ⟨3874271330144521462189637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2582847553429680974793091 3874271330144521462189637)
                ·
                  refine ⟨726425874402097774160557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3874271330144521462189637 726425874402097774160557)
                  ·
                    refine ⟨272409702900786665310209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 726425874402097774160557 272409702900786665310209)
                    ·
                      refine ⟨204307277175589998982657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 272409702900786665310209 204307277175589998982657)
                      ·
                        rfl

theorem cell23_397887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4, 3, 2].length) (baseStart_397887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397887 prefixEnd_397887 := by exact prefixLift 397887
  have htrace : WordTrace (prefixWord ++ tailWord_397887) baseStart_397887 baseEnd_397887 := by
    simpa [prefixWord, tailWord_397887, baseEnd_397887] using wordTrace_append hprefix tailTrace_397887
  have hstable : (prefixWord ++ tailWord_397887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397887).length < 2 ^ (prefixWord ++ tailWord_397887).sum := by decide
  have hdescent : baseEnd_397887 < baseStart_397887 := by decide
  rcases family_descends (prefixWord ++ tailWord_397887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397934 : List Nat := [4, 1, 2, 2, 2, 1, 2, 3, 1, 1, 4]
def baseStart_397934 : Nat := 118140960795 + 397934 * 2 ^ 59
def prefixEnd_397934 : Nat := 4983230072969 + 3 ^ 40 * 397934 * 2
def baseEnd_397934 : Nat := 204331410766351315094941

theorem tailTrace_397934 : CollatzResearch.WordTrace tailWord_397934 prefixEnd_397934 204331410766351315094941 := by
  unfold tailWord_397934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1814230667545069320200107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9675896893573703041067237 1814230667545069320200107)
  ·
    refine ⟨2721346001317603980300161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1814230667545069320200107 2721346001317603980300161)
    ·
      refine ⟨2041009500988202985225121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2721346001317603980300161 2041009500988202985225121)
      ·
        refine ⟨1530757125741152238918841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2041009500988202985225121 1530757125741152238918841)
        ·
          refine ⟨1148067844305864179189131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1530757125741152238918841 1148067844305864179189131)
          ·
            refine ⟨1722101766458796268783697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1148067844305864179189131 1722101766458796268783697)
            ·
              refine ⟨1291576324844097201587773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1722101766458796268783697 1291576324844097201587773)
              ·
                refine ⟨484341121816536450595415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1291576324844097201587773 484341121816536450595415)
                ·
                  refine ⟨726511682724804675893123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 484341121816536450595415 726511682724804675893123)
                  ·
                    refine ⟨1089767524087207013839685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 726511682724804675893123 1089767524087207013839685)
                    ·
                      refine ⟨204331410766351315094941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1089767524087207013839685 204331410766351315094941)
                      ·
                        rfl

theorem cell23_397934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_397934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397934 prefixEnd_397934 := by exact prefixLift 397934
  have htrace : WordTrace (prefixWord ++ tailWord_397934) baseStart_397934 baseEnd_397934 := by
    simpa [prefixWord, tailWord_397934, baseEnd_397934] using wordTrace_append hprefix tailTrace_397934
  have hstable : (prefixWord ++ tailWord_397934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397934).length < 2 ^ (prefixWord ++ tailWord_397934).sum := by decide
  have hdescent : baseEnd_397934 < baseStart_397934 := by decide
  rcases family_descends (prefixWord ++ tailWord_397934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397984 : List Nat := [2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 3]
def baseStart_397984 : Nat := 118140960795 + 397984 * 2 ^ 59
def prefixEnd_397984 : Nat := 4983230072969 + 3 ^ 40 * 397984 * 2
def baseEnd_397984 : Nat := 204357084799076119469711

theorem tailTrace_397984 : CollatzResearch.WordTrace tailWord_397984 prefixEnd_397984 204357084799076119469711 := by
  unfold tailWord_397984
  simp only [CollatzResearch.WordTrace]
  refine ⟨7257834495089706550460503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9677112660119608733947337 7257834495089706550460503)
  ·
    refine ⟨10886751742634559825690755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7257834495089706550460503 10886751742634559825690755)
    ·
      refine ⟨16330127613951839738536133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10886751742634559825690755 16330127613951839738536133)
      ·
        refine ⟨3061898927615969950975525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16330127613951839738536133 3061898927615969950975525)
        ·
          refine ⟨574106048927994365807911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3061898927615969950975525 574106048927994365807911)
          ·
            refine ⟨861159073391991548711867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 574106048927994365807911 861159073391991548711867)
            ·
              refine ⟨1291738610087987323067801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 861159073391991548711867 1291738610087987323067801)
              ·
                refine ⟨968803957565990492300851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1291738610087987323067801 968803957565990492300851)
                ·
                  refine ⟨1453205936348985738451277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 968803957565990492300851 1453205936348985738451277)
                  ·
                    refine ⟨544952226130869651919229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1453205936348985738451277 544952226130869651919229)
                    ·
                      refine ⟨204357084799076119469711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 544952226130869651919229 204357084799076119469711)
                      ·
                        rfl

theorem cell23_397984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_397984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_397984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_397984 prefixEnd_397984 := by exact prefixLift 397984
  have htrace : WordTrace (prefixWord ++ tailWord_397984) baseStart_397984 baseEnd_397984 := by
    simpa [prefixWord, tailWord_397984, baseEnd_397984] using wordTrace_append hprefix tailTrace_397984
  have hstable : (prefixWord ++ tailWord_397984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397984).length < 2 ^ (prefixWord ++ tailWord_397984).sum := by decide
  have hdescent : baseEnd_397984 < baseStart_397984 := by decide
  rcases family_descends (prefixWord ++ tailWord_397984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398000 : List Nat := [2, 1, 1, 1, 2, 1, 3, 4, 2, 6]
def baseStart_398000 : Nat := 118140960795 + 398000 * 2 ^ 59
def prefixEnd_398000 : Nat := 4983230072969 + 3 ^ 40 * 398000 * 2
def baseEnd_398000 : Nat := 68121766829849352289879

theorem tailTrace_398000 : CollatzResearch.WordTrace tailWord_398000 prefixEnd_398000 68121766829849352289879 := by
  unfold tailWord_398000
  simp only [CollatzResearch.WordTrace]
  refine ⟨7258126279060723916751727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9677501705414298555668969 7258126279060723916751727)
  ·
    refine ⟨10887189418591085875127591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7258126279060723916751727 10887189418591085875127591)
    ·
      refine ⟨16330784127886628812691387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10887189418591085875127591 16330784127886628812691387)
      ·
        refine ⟨24496176191829943219037081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16330784127886628812691387 24496176191829943219037081)
        ·
          refine ⟨18372132143872457414277811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24496176191829943219037081 18372132143872457414277811)
          ·
            refine ⟨27558198215808686121416717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18372132143872457414277811 27558198215808686121416717)
            ·
              refine ⟨10334324330928257295531269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27558198215808686121416717 10334324330928257295531269)
              ·
                refine ⟨1937685812049048242912113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10334324330928257295531269 1937685812049048242912113)
                ·
                  refine ⟨1453264359036786182184085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1937685812049048242912113 1453264359036786182184085)
                  ·
                    refine ⟨68121766829849352289879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1453264359036786182184085 68121766829849352289879)
                    ·
                      rfl

theorem cell23_398000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 2, 6].length) (baseStart_398000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_398000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_398000 prefixEnd_398000 := by exact prefixLift 398000
  have htrace : WordTrace (prefixWord ++ tailWord_398000) baseStart_398000 baseEnd_398000 := by
    simpa [prefixWord, tailWord_398000, baseEnd_398000] using wordTrace_append hprefix tailTrace_398000
  have hstable : (prefixWord ++ tailWord_398000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398000).length < 2 ^ (prefixWord ++ tailWord_398000).sum := by decide
  have hdescent : baseEnd_398000 < baseStart_398000 := by decide
  rcases family_descends (prefixWord ++ tailWord_398000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398024 : List Nat := [2, 1, 3, 1, 2, 3, 1, 3, 1, 4, 2]
def baseStart_398024 : Nat := 118140960795 + 398024 * 2 ^ 59
def prefixEnd_398024 : Nat := 4983230072969 + 3 ^ 40 * 398024 * 2
def baseEnd_398024 : Nat := 204377624025255962969527

theorem tailTrace_398024 : CollatzResearch.WordTrace tailWord_398024 prefixEnd_398024 204377624025255962969527 := by
  unfold tailWord_398024
  simp only [CollatzResearch.WordTrace]
  refine ⟨7258563955017249966188563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9678085273356333288251417 7258563955017249966188563)
  ·
    refine ⟨10887845932525874949282845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7258563955017249966188563 10887845932525874949282845)
    ·
      refine ⟨4082942224697203105981067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10887845932525874949282845 4082942224697203105981067)
      ·
        refine ⟨6124413337045804658971601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4082942224697203105981067 6124413337045804658971601)
        ·
          refine ⟨4593310002784353494228701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6124413337045804658971601 4593310002784353494228701)
          ·
            refine ⟨1722491251044132560335763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4593310002784353494228701 1722491251044132560335763)
            ·
              refine ⟨2583736876566198840503645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1722491251044132560335763 2583736876566198840503645)
              ·
                refine ⟨968901328712324565188867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2583736876566198840503645 968901328712324565188867)
                ·
                  refine ⟨1453351993068486847783301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 968901328712324565188867 1453351993068486847783301)
                  ·
                    refine ⟨272503498700341283959369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1453351993068486847783301 272503498700341283959369)
                    ·
                      refine ⟨204377624025255962969527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 272503498700341283959369 204377624025255962969527)
                      ·
                        rfl

theorem cell23_398024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 1, 4, 2].length) (baseStart_398024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_398024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_398024 prefixEnd_398024 := by exact prefixLift 398024
  have htrace : WordTrace (prefixWord ++ tailWord_398024) baseStart_398024 baseEnd_398024 := by
    simpa [prefixWord, tailWord_398024, baseEnd_398024] using wordTrace_append hprefix tailTrace_398024
  have hstable : (prefixWord ++ tailWord_398024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398024).length < 2 ^ (prefixWord ++ tailWord_398024).sum := by decide
  have hdescent : baseEnd_398024 < baseStart_398024 := by decide
  rcases family_descends (prefixWord ++ tailWord_398024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398057 : List Nat := [1, 2, 1, 1, 1, 2, 5, 2, 2, 3, 3]
def baseStart_398057 : Nat := 118140960795 + 398057 * 2 ^ 59
def prefixEnd_398057 : Nat := 4983230072969 + 3 ^ 40 * 398057 * 2
def baseEnd_398057 : Nat := 204394568886854333856875

theorem tailTrace_398057 : CollatzResearch.WordTrace tailWord_398057 prefixEnd_398057 204394568886854333856875 := by
  unfold tailWord_398057
  simp only [CollatzResearch.WordTrace]
  refine ⟨14518331518914946568328425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9678887679276631045552283 14518331518914946568328425)
  ·
    refine ⟨10888748639186209926246319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14518331518914946568328425 10888748639186209926246319)
    ·
      refine ⟨16333122958779314889369479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10888748639186209926246319 16333122958779314889369479)
      ·
        refine ⟨24499684438168972334054219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16333122958779314889369479 24499684438168972334054219)
        ·
          refine ⟨36749526657253458501081329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24499684438168972334054219 36749526657253458501081329)
          ·
            refine ⟨27562144992940093875810997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36749526657253458501081329 27562144992940093875810997)
            ·
              refine ⟨2583951093088133800857281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27562144992940093875810997 2583951093088133800857281)
              ·
                refine ⟨1937963319816100350642961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2583951093088133800857281 1937963319816100350642961)
                ·
                  refine ⟨1453472489862075262982221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1937963319816100350642961 1453472489862075262982221)
                  ·
                    refine ⟨545052183698278223618333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1453472489862075262982221 545052183698278223618333)
                    ·
                      refine ⟨204394568886854333856875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 545052183698278223618333 204394568886854333856875)
                      ·
                        rfl

theorem cell23_398057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 3, 3].length) (baseStart_398057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_398057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_398057 prefixEnd_398057 := by exact prefixLift 398057
  have htrace : WordTrace (prefixWord ++ tailWord_398057) baseStart_398057 baseEnd_398057 := by
    simpa [prefixWord, tailWord_398057, baseEnd_398057] using wordTrace_append hprefix tailTrace_398057
  have hstable : (prefixWord ++ tailWord_398057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398057).length < 2 ^ (prefixWord ++ tailWord_398057).sum := by decide
  have hdescent : baseEnd_398057 < baseStart_398057 := by decide
  rcases family_descends (prefixWord ++ tailWord_398057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398097 : List Nat := [1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 4]
def baseStart_398097 : Nat := 118140960795 + 398097 * 2 ^ 59
def prefixEnd_398097 : Nat := 4983230072969 + 3 ^ 40 * 398097 * 2
def baseEnd_398097 : Nat := 204415108113034177356691

theorem tailTrace_398097 : CollatzResearch.WordTrace tailWord_398097 prefixEnd_398097 204415108113034177356691 := by
  unfold tailWord_398097
  simp only [CollatzResearch.WordTrace]
  refine ⟨14519790438770033399784545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9679860292513355599856363 14519790438770033399784545)
  ·
    refine ⟨10889842829077525049838409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14519790438770033399784545 10889842829077525049838409)
    ·
      refine ⟨8167382121808143787378807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10889842829077525049838409 8167382121808143787378807)
      ·
        refine ⟨12251073182712215681068211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8167382121808143787378807 12251073182712215681068211)
        ·
          refine ⟨18376609774068323521602317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12251073182712215681068211 18376609774068323521602317)
          ·
            refine ⟨6891228665275621320600869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18376609774068323521602317 6891228665275621320600869)
            ·
              refine ⟨1292105374739178997612663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6891228665275621320600869 1292105374739178997612663)
              ·
                refine ⟨1938158062108768496418995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1292105374739178997612663 1938158062108768496418995)
                ·
                  refine ⟨2907237093163152744628493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1938158062108768496418995 2907237093163152744628493)
                  ·
                    refine ⟨1090213909936182279235685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2907237093163152744628493 1090213909936182279235685)
                    ·
                      refine ⟨204415108113034177356691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1090213909936182279235685 204415108113034177356691)
                      ·
                        rfl

theorem cell23_398097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 4].length) (baseStart_398097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_398097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_398097 prefixEnd_398097 := by exact prefixLift 398097
  have htrace : WordTrace (prefixWord ++ tailWord_398097) baseStart_398097 baseEnd_398097 := by
    simpa [prefixWord, tailWord_398097, baseEnd_398097] using wordTrace_append hprefix tailTrace_398097
  have hstable : (prefixWord ++ tailWord_398097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398097).length < 2 ^ (prefixWord ++ tailWord_398097).sum := by decide
  have hdescent : baseEnd_398097 < baseStart_398097 := by decide
  rcases family_descends (prefixWord ++ tailWord_398097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398114 : List Nat := [3, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4]
def baseStart_398114 : Nat := 118140960795 + 398114 * 2 ^ 59
def prefixEnd_398114 : Nat := 4983230072969 + 3 ^ 40 * 398114 * 2
def baseEnd_398114 : Nat := 204423837284160610844113

theorem tailTrace_398114 : CollatzResearch.WordTrace tailWord_398114 prefixEnd_398114 204423837284160610844113 := by
  unfold tailWord_398114
  simp only [CollatzResearch.WordTrace]
  refine ⟨3630102619927111325788349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9680273653138963535435597 3630102619927111325788349)
  ·
    refine ⟨1361288482472666747170631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3630102619927111325788349 1361288482472666747170631)
    ·
      refine ⟨2041932723709000120755947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1361288482472666747170631 2041932723709000120755947)
      ·
        refine ⟨3062899085563500181133921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2041932723709000120755947 3062899085563500181133921)
        ·
          refine ⟨2297174314172625135850441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3062899085563500181133921 2297174314172625135850441)
          ·
            refine ⟨1722880735629468851887831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2297174314172625135850441 1722880735629468851887831)
            ·
              refine ⟨2584321103444203277831747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1722880735629468851887831 2584321103444203277831747)
              ·
                refine ⟨3876481655166304916747621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2584321103444203277831747 3876481655166304916747621)
                ·
                  refine ⟨726840310343682171890179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3876481655166304916747621 726840310343682171890179)
                  ·
                    refine ⟨1090260465515523257835269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 726840310343682171890179 1090260465515523257835269)
                    ·
                      refine ⟨204423837284160610844113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1090260465515523257835269 204423837284160610844113)
                      ·
                        rfl

theorem cell23_398114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_398114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_398114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_398114 prefixEnd_398114 := by exact prefixLift 398114
  have htrace : WordTrace (prefixWord ++ tailWord_398114) baseStart_398114 baseEnd_398114 := by
    simpa [prefixWord, tailWord_398114, baseEnd_398114] using wordTrace_append hprefix tailTrace_398114
  have hstable : (prefixWord ++ tailWord_398114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398114).length < 2 ^ (prefixWord ++ tailWord_398114).sum := by decide
  have hdescent : baseEnd_398114 < baseStart_398114 := by decide
  rcases family_descends (prefixWord ++ tailWord_398114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398184 : List Nat := [2, 1, 4, 2, 1, 2, 1, 2, 3, 5]
def baseStart_398184 : Nat := 118140960795 + 398184 * 2 ^ 59
def prefixEnd_398184 : Nat := 4983230072969 + 3 ^ 40 * 398184 * 2
def baseEnd_398184 : Nat := 68153260309991778989597

theorem tailTrace_398184 : CollatzResearch.WordTrace tailWord_398184 prefixEnd_398184 68153260309991778989597 := by
  unfold tailWord_398184
  simp only [CollatzResearch.WordTrace]
  refine ⟨7261481794727423629100803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9681975726303231505467737 7261481794727423629100803)
  ·
    refine ⟨10892222692091135443651205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7261481794727423629100803 10892222692091135443651205)
    ·
      refine ⟨2042291754767087895684601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10892222692091135443651205 2042291754767087895684601)
      ·
        refine ⟨1531718816075315921763451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2042291754767087895684601 1531718816075315921763451)
        ·
          refine ⟨2297578224112973882645177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1531718816075315921763451 2297578224112973882645177)
          ·
            refine ⟨1723183668084730411983883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2297578224112973882645177 1723183668084730411983883)
            ·
              refine ⟨2584775502127095617975825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1723183668084730411983883 2584775502127095617975825)
              ·
                refine ⟨1938581626595321713481869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2584775502127095617975825 1938581626595321713481869)
                ·
                  refine ⟨726968109973245642555701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1938581626595321713481869 726968109973245642555701)
                  ·
                    refine ⟨68153260309991778989597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 726968109973245642555701 68153260309991778989597)
                    ·
                      rfl

theorem cell23_398184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_398184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_398184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_398184 prefixEnd_398184 := by exact prefixLift 398184
  have htrace : WordTrace (prefixWord ++ tailWord_398184) baseStart_398184 baseEnd_398184 := by
    simpa [prefixWord, tailWord_398184, baseEnd_398184] using wordTrace_append hprefix tailTrace_398184
  have hstable : (prefixWord ++ tailWord_398184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398184).length < 2 ^ (prefixWord ++ tailWord_398184).sum := by decide
  have hdescent : baseEnd_398184 < baseStart_398184 := by decide
  rcases family_descends (prefixWord ++ tailWord_398184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398198 : List Nat := [5, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3]
def baseStart_398198 : Nat := 118140960795 + 398198 * 2 ^ 59
def prefixEnd_398198 : Nat := 4983230072969 + 3 ^ 40 * 398198 * 2
def baseEnd_398198 : Nat := 204466969659138282193727

theorem tailTrace_398198 : CollatzResearch.WordTrace tailWord_398198 prefixEnd_398198 204466969659138282193727 := by
  unfold tailWord_398198
  simp only [CollatzResearch.WordTrace]
  refine ⟨907717138212757978075703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9682316140936085099474165 907717138212757978075703)
  ·
    refine ⟨1361575707319136967113555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 907717138212757978075703 1361575707319136967113555)
    ·
      refine ⟨2042363560978705450670333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1361575707319136967113555 2042363560978705450670333)
      ·
        refine ⟨765886335367014544001375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2042363560978705450670333 765886335367014544001375)
        ·
          refine ⟨1148829503050521816002063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 765886335367014544001375 1148829503050521816002063)
          ·
            refine ⟨1723244254575782724003095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1148829503050521816002063 1723244254575782724003095)
            ·
              refine ⟨2584866381863674086004643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1723244254575782724003095 2584866381863674086004643)
              ·
                refine ⟨3877299572795511129006965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2584866381863674086004643 3877299572795511129006965)
                ·
                  refine ⟨363496834949579168344403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3877299572795511129006965 363496834949579168344403)
                  ·
                    refine ⟨545245252424368752516605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 363496834949579168344403 545245252424368752516605)
                    ·
                      refine ⟨204466969659138282193727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 545245252424368752516605 204466969659138282193727)
                      ·
                        rfl

theorem cell23_398198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_398198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_398198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_398198 prefixEnd_398198 := by exact prefixLift 398198
  have htrace : WordTrace (prefixWord ++ tailWord_398198) baseStart_398198 baseEnd_398198 := by
    simpa [prefixWord, tailWord_398198, baseEnd_398198] using wordTrace_append hprefix tailTrace_398198
  have hstable : (prefixWord ++ tailWord_398198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398198).length < 2 ^ (prefixWord ++ tailWord_398198).sum := by decide
  have hdescent : baseEnd_398198 < baseStart_398198 := by decide
  rcases family_descends (prefixWord ++ tailWord_398198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398215 : List Nat := [1, 1, 4, 2, 3, 2, 2, 3, 1, 1, 3]
def baseStart_398215 : Nat := 118140960795 + 398215 * 2 ^ 59
def prefixEnd_398215 : Nat := 4983230072969 + 3 ^ 40 * 398215 * 2
def baseEnd_398215 : Nat := 204475698830264715681149

theorem tailTrace_398215 : CollatzResearch.WordTrace tailWord_398215 prefixEnd_398215 204475698830264715681149 := by
  unfold tailWord_398215
  simp only [CollatzResearch.WordTrace]
  refine ⟨14524094252342539552580099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9682729501561693035053399 14524094252342539552580099)
  ·
    refine ⟨21786141378513809328870149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14524094252342539552580099 21786141378513809328870149)
    ·
      refine ⟨4084901508471339249163153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21786141378513809328870149 4084901508471339249163153)
      ·
        refine ⟨3063676131353504436872365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4084901508471339249163153 3063676131353504436872365)
        ·
          refine ⟨1148878549257564163827137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3063676131353504436872365 1148878549257564163827137)
          ·
            refine ⟨861658911943173122870353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1148878549257564163827137 861658911943173122870353)
            ·
              refine ⟨646244183957379842152765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 861658911943173122870353 646244183957379842152765)
              ·
                refine ⟨242341568984017440807287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 646244183957379842152765 242341568984017440807287)
                ·
                  refine ⟨363512353476026161210931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 242341568984017440807287 363512353476026161210931)
                  ·
                    refine ⟨545268530214039241816397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 363512353476026161210931 545268530214039241816397)
                    ·
                      refine ⟨204475698830264715681149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 545268530214039241816397 204475698830264715681149)
                      ·
                        rfl

theorem cell23_398215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 3, 1, 1, 3].length) (baseStart_398215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_398215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_398215 prefixEnd_398215 := by exact prefixLift 398215
  have htrace : WordTrace (prefixWord ++ tailWord_398215) baseStart_398215 baseEnd_398215 := by
    simpa [prefixWord, tailWord_398215, baseEnd_398215] using wordTrace_append hprefix tailTrace_398215
  have hstable : (prefixWord ++ tailWord_398215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398215).length < 2 ^ (prefixWord ++ tailWord_398215).sum := by decide
  have hdescent : baseEnd_398215 < baseStart_398215 := by decide
  rcases family_descends (prefixWord ++ tailWord_398215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398218 : List Nat := [3, 1, 2, 4, 1, 1, 4, 1, 1, 5]
def baseStart_398218 : Nat := 118140960795 + 398218 * 2 ^ 59
def prefixEnd_398218 : Nat := 4983230072969 + 3 ^ 40 * 398218 * 2
def baseEnd_398218 : Nat := 68159079757409401314545

theorem tailTrace_398218 : CollatzResearch.WordTrace tailWord_398218 prefixEnd_398218 68159079757409401314545 := by
  unfold tailWord_398218
  simp only [CollatzResearch.WordTrace]
  refine ⟨3631050917832917766234827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9682802447554447376626205 3631050917832917766234827)
  ·
    refine ⟨5446576376749376649352241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3631050917832917766234827 5446576376749376649352241)
    ·
      refine ⟨4084932282562032487014181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5446576376749376649352241 4084932282562032487014181)
      ·
        refine ⟨765924802980381091315159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4084932282562032487014181 765924802980381091315159)
        ·
          refine ⟨1148887204470571636972739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 765924802980381091315159 1148887204470571636972739)
          ·
            refine ⟨1723330806705857455459109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1148887204470571636972739 1723330806705857455459109)
            ·
              refine ⟨323124526257348272898583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1723330806705857455459109 323124526257348272898583)
              ·
                refine ⟨484686789386022409347875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 323124526257348272898583 484686789386022409347875)
                ·
                  refine ⟨727030184079033614021813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 484686789386022409347875 727030184079033614021813)
                  ·
                    refine ⟨68159079757409401314545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 727030184079033614021813 68159079757409401314545)
                    ·
                      rfl

theorem cell23_398218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 1, 1, 5].length) (baseStart_398218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_398218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_398218 prefixEnd_398218 := by exact prefixLift 398218
  have htrace : WordTrace (prefixWord ++ tailWord_398218) baseStart_398218 baseEnd_398218 := by
    simpa [prefixWord, tailWord_398218, baseEnd_398218] using wordTrace_append hprefix tailTrace_398218
  have hstable : (prefixWord ++ tailWord_398218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398218).length < 2 ^ (prefixWord ++ tailWord_398218).sum := by decide
  have hdescent : baseEnd_398218 < baseStart_398218 := by decide
  rcases family_descends (prefixWord ++ tailWord_398218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398241 : List Nat := [1, 2, 3, 4, 1, 2, 1, 2, 1, 1, 5]
def baseStart_398241 : Nat := 118140960795 + 398241 * 2 ^ 59
def prefixEnd_398241 : Nat := 4983230072969 + 3 ^ 40 * 398241 * 2
def baseEnd_398241 : Nat := 204489049327281613956029

theorem tailTrace_398241 : CollatzResearch.WordTrace tailWord_398241 prefixEnd_398241 204489049327281613956029 := by
  unfold tailWord_398241
  simp only [CollatzResearch.WordTrace]
  refine ⟨14525042550248345993026577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9683361700165563995351051 14525042550248345993026577)
  ·
    refine ⟨10893781912686259494769933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14525042550248345993026577 10893781912686259494769933)
    ·
      refine ⟨4085168217257347310538725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10893781912686259494769933 4085168217257347310538725)
      ·
        refine ⟨765969040735752620726011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4085168217257347310538725 765969040735752620726011)
        ·
          refine ⟨1148953561103628931089017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 765969040735752620726011 1148953561103628931089017)
          ·
            refine ⟨861715170827721698316763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1148953561103628931089017 861715170827721698316763)
            ·
              refine ⟨1292572756241582547475145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 861715170827721698316763 1292572756241582547475145)
              ·
                refine ⟨969429567181186910606359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1292572756241582547475145 969429567181186910606359)
                ·
                  refine ⟨1454144350771780365909539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 969429567181186910606359 1454144350771780365909539)
                  ·
                    refine ⟨2181216526157670548864309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1454144350771780365909539 2181216526157670548864309)
                    ·
                      refine ⟨204489049327281613956029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2181216526157670548864309 204489049327281613956029)
                      ·
                        rfl

theorem cell23_398241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_398241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_398241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_398241 prefixEnd_398241 := by exact prefixLift 398241
  have htrace : WordTrace (prefixWord ++ tailWord_398241) baseStart_398241 baseEnd_398241 := by
    simpa [prefixWord, tailWord_398241, baseEnd_398241] using wordTrace_append hprefix tailTrace_398241
  have hstable : (prefixWord ++ tailWord_398241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398241).length < 2 ^ (prefixWord ++ tailWord_398241).sum := by decide
  have hdescent : baseEnd_398241 < baseStart_398241 := by decide
  rcases family_descends (prefixWord ++ tailWord_398241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398267 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 7]
def baseStart_398267 : Nat := 118140960795 + 398267 * 2 ^ 59
def prefixEnd_398267 : Nat := 4983230072969 + 3 ^ 40 * 398267 * 2
def baseEnd_398267 : Nat := 204502399824298512230909

theorem tailTrace_398267 : CollatzResearch.WordTrace tailWord_398267 prefixEnd_398267 204502399824298512230909 := by
  unfold tailWord_398267
  simp only [CollatzResearch.WordTrace]
  refine ⟨14525990848154152433473055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9683993898769434955648703 14525990848154152433473055)
  ·
    refine ⟨21788986272231228650209583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14525990848154152433473055 21788986272231228650209583)
    ·
      refine ⟨32683479408346842975314375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21788986272231228650209583 32683479408346842975314375)
      ·
        refine ⟨49025219112520264462971563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32683479408346842975314375 49025219112520264462971563)
        ·
          refine ⟨73537828668780396694457345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49025219112520264462971563 73537828668780396694457345)
          ·
            refine ⟨55153371501585297520843009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73537828668780396694457345 55153371501585297520843009)
            ·
              refine ⟨41365028626188973140632257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55153371501585297520843009 41365028626188973140632257)
              ·
                refine ⟨31023771469641729855474193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41365028626188973140632257 31023771469641729855474193)
                ·
                  refine ⟨23267828602231297391605645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31023771469641729855474193 23267828602231297391605645)
                  ·
                    refine ⟨8725435725836736521852117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23267828602231297391605645 8725435725836736521852117)
                    ·
                      refine ⟨204502399824298512230909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 8725435725836736521852117 204502399824298512230909)
                      ·
                        rfl

theorem cell23_398267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 7].length) (baseStart_398267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_398267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_398267 prefixEnd_398267 := by exact prefixLift 398267
  have htrace : WordTrace (prefixWord ++ tailWord_398267) baseStart_398267 baseEnd_398267 := by
    simpa [prefixWord, tailWord_398267, baseEnd_398267] using wordTrace_append hprefix tailTrace_398267
  have hstable : (prefixWord ++ tailWord_398267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398267).length < 2 ^ (prefixWord ++ tailWord_398267).sum := by decide
  have hdescent : baseEnd_398267 < baseStart_398267 := by decide
  rcases family_descends (prefixWord ++ tailWord_398267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398272 : List Nat := [2, 1, 1, 2, 3, 5, 1, 3, 1, 2, 2]
def baseStart_398272 : Nat := 118140960795 + 398272 * 2 ^ 59
def prefixEnd_398272 : Nat := 4983230072969 + 3 ^ 40 * 398272 * 2
def baseEnd_398272 : Nat := 204504967227570992668387

theorem tailTrace_398272 : CollatzResearch.WordTrace tailWord_398272 prefixEnd_398272 204504967227570992668387 := by
  unfold tailWord_398272
  simp only [CollatzResearch.WordTrace]
  refine ⟨7263086606568019143702535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9684115475424025524936713 7263086606568019143702535)
  ·
    refine ⟨10894629909852028715553803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7263086606568019143702535 10894629909852028715553803)
    ·
      refine ⟨16341944864778043073330705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10894629909852028715553803 16341944864778043073330705)
      ·
        refine ⟨12256458648583532304998029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16341944864778043073330705 12256458648583532304998029)
        ·
          refine ⟨4596171993218824614374261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12256458648583532304998029 4596171993218824614374261)
          ·
            refine ⟨430891124364264807597587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4596171993218824614374261 430891124364264807597587)
            ·
              refine ⟨646336686546397211396381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 430891124364264807597587 646336686546397211396381)
              ·
                refine ⟨242376257454898954273643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 646336686546397211396381 242376257454898954273643)
                ·
                  refine ⟨363564386182348431410465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 242376257454898954273643 363564386182348431410465)
                  ·
                    refine ⟨272673289636761323557849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 363564386182348431410465 272673289636761323557849)
                    ·
                      refine ⟨204504967227570992668387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 272673289636761323557849 204504967227570992668387)
                      ·
                        rfl

theorem cell23_398272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 3, 1, 2, 2].length) (baseStart_398272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_398272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_398272 prefixEnd_398272 := by exact prefixLift 398272
  have htrace : WordTrace (prefixWord ++ tailWord_398272) baseStart_398272 baseEnd_398272 := by
    simpa [prefixWord, tailWord_398272, baseEnd_398272] using wordTrace_append hprefix tailTrace_398272
  have hstable : (prefixWord ++ tailWord_398272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398272).length < 2 ^ (prefixWord ++ tailWord_398272).sum := by decide
  have hdescent : baseEnd_398272 < baseStart_398272 := by decide
  rcases family_descends (prefixWord ++ tailWord_398272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398284 : List Nat := [2, 2, 1, 4, 1, 1, 1, 2, 2, 2, 5]
def baseStart_398284 : Nat := 118140960795 + 398284 * 2 ^ 59
def prefixEnd_398284 : Nat := 4983230072969 + 3 ^ 40 * 398284 * 2
def baseEnd_398284 : Nat := 204511128995424945718331

theorem tailTrace_398284 : CollatzResearch.WordTrace tailWord_398284 prefixEnd_398284 204511128995424945718331 := by
  unfold tailWord_398284
  simp only [CollatzResearch.WordTrace]
  refine ⟨7263305444546282168420953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9684407259395042891227937 7263305444546282168420953)
  ·
    refine ⟨5447479083409711626315715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7263305444546282168420953 5447479083409711626315715)
    ·
      refine ⟨8171218625114567439473573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5447479083409711626315715 8171218625114567439473573)
      ·
        refine ⟨1532103492208981394901295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8171218625114567439473573 1532103492208981394901295)
        ·
          refine ⟨2298155238313472092351943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1532103492208981394901295 2298155238313472092351943)
          ·
            refine ⟨3447232857470208138527915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2298155238313472092351943 3447232857470208138527915)
            ·
              refine ⟨5170849286205312207791873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3447232857470208138527915 5170849286205312207791873)
              ·
                refine ⟨3878136964653984155843905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5170849286205312207791873 3878136964653984155843905)
                ·
                  refine ⟨2908602723490488116882929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3878136964653984155843905 2908602723490488116882929)
                  ·
                    refine ⟨2181452042617866087662197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2908602723490488116882929 2181452042617866087662197)
                    ·
                      refine ⟨204511128995424945718331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2181452042617866087662197 204511128995424945718331)
                      ·
                        rfl

theorem cell23_398284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_398284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_398284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_398284 prefixEnd_398284 := by exact prefixLift 398284
  have htrace : WordTrace (prefixWord ++ tailWord_398284) baseStart_398284 baseEnd_398284 := by
    simpa [prefixWord, tailWord_398284, baseEnd_398284] using wordTrace_append hprefix tailTrace_398284
  have hstable : (prefixWord ++ tailWord_398284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398284).length < 2 ^ (prefixWord ++ tailWord_398284).sum := by decide
  have hdescent : baseEnd_398284 < baseStart_398284 := by decide
  rcases family_descends (prefixWord ++ tailWord_398284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398368 : List Nat := [2, 1, 1, 7, 1, 1, 1, 2, 7]
def baseStart_398368 : Nat := 118140960795 + 398368 * 2 ^ 59
def prefixEnd_398368 : Nat := 4983230072969 + 3 ^ 40 * 398368 * 2
def baseEnd_398368 : Nat := 22728251263378068563105

theorem tailTrace_398368 : CollatzResearch.WordTrace tailWord_398368 prefixEnd_398368 22728251263378068563105 := by
  unfold tailWord_398368
  simp only [CollatzResearch.WordTrace]
  refine ⟨7264837310394123341449879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9686449747192164455266505 7264837310394123341449879)
  ·
    refine ⟨10897255965591185012174819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7264837310394123341449879 10897255965591185012174819)
    ·
      refine ⟨16345883948386777518262229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10897255965591185012174819 16345883948386777518262229)
      ·
        refine ⟨383106655040315098084271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 16345883948386777518262229 383106655040315098084271)
        ·
          refine ⟨574659982560472647126407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383106655040315098084271 574659982560472647126407)
          ·
            refine ⟨861989973840708970689611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 574659982560472647126407 861989973840708970689611)
            ·
              refine ⟨1292984960761063456034417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 861989973840708970689611 1292984960761063456034417)
              ·
                refine ⟨969738720570797592025813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1292984960761063456034417 969738720570797592025813)
                ·
                  refine ⟨22728251263378068563105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 969738720570797592025813 22728251263378068563105)
                  ·
                    rfl

theorem cell23_398368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 7].length) (baseStart_398368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_398368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_398368 prefixEnd_398368 := by exact prefixLift 398368
  have htrace : WordTrace (prefixWord ++ tailWord_398368) baseStart_398368 baseEnd_398368 := by
    simpa [prefixWord, tailWord_398368, baseEnd_398368] using wordTrace_append hprefix tailTrace_398368
  have hstable : (prefixWord ++ tailWord_398368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398368).length < 2 ^ (prefixWord ++ tailWord_398368).sum := by decide
  have hdescent : baseEnd_398368 < baseStart_398368 := by decide
  rcases family_descends (prefixWord ++ tailWord_398368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398421 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 3, 4, 3]
def baseStart_398421 : Nat := 118140960795 + 398421 * 2 ^ 59
def prefixEnd_398421 : Nat := 4983230072969 + 3 ^ 40 * 398421 * 2
def baseEnd_398421 : Nat := 204581475845090909705201

theorem tailTrace_398421 : CollatzResearch.WordTrace tailWord_398421 prefixEnd_398421 204581475845090909705201 := by
  unfold tailWord_398421
  simp only [CollatzResearch.WordTrace]
  refine ⟨14531607689596236734579117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9687738459730824489719411 14531607689596236734579117)
  ·
    refine ⟨5449352883598588775467169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14531607689596236734579117 5449352883598588775467169)
    ·
      refine ⟨4087014662698941581600377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5449352883598588775467169 4087014662698941581600377)
      ·
        refine ⟨3065260997024206186200283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4087014662698941581600377 3065260997024206186200283)
        ·
          refine ⟨4597891495536309279300425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3065260997024206186200283 4597891495536309279300425)
          ·
            refine ⟨3448418621652231959475319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4597891495536309279300425 3448418621652231959475319)
            ·
              refine ⟨5172627932478347939212979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3448418621652231959475319 5172627932478347939212979)
              ·
                refine ⟨7758941898717521908819469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5172627932478347939212979 7758941898717521908819469)
                ·
                  refine ⟨2909603212019070715807301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7758941898717521908819469 2909603212019070715807301)
                  ·
                    refine ⟨545550602253575759213869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2909603212019070715807301 545550602253575759213869)
                    ·
                      refine ⟨204581475845090909705201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 545550602253575759213869 204581475845090909705201)
                      ·
                        rfl

theorem cell23_398421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_398421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_398421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_398421 prefixEnd_398421 := by exact prefixLift 398421
  have htrace : WordTrace (prefixWord ++ tailWord_398421) baseStart_398421 baseEnd_398421 := by
    simpa [prefixWord, tailWord_398421, baseEnd_398421] using wordTrace_append hprefix tailTrace_398421
  have hstable : (prefixWord ++ tailWord_398421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398421).length < 2 ^ (prefixWord ++ tailWord_398421).sum := by decide
  have hdescent : baseEnd_398421 < baseStart_398421 := by decide
  rcases family_descends (prefixWord ++ tailWord_398421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398428 : List Nat := [2, 2, 4, 1, 1, 1, 1, 4, 3, 4]
def baseStart_398428 : Nat := 118140960795 + 398428 * 2 ^ 59
def prefixEnd_398428 : Nat := 4983230072969 + 3 ^ 40 * 398428 * 2
def baseEnd_398428 : Nat := 68195023403224127439223

theorem tailTrace_398428 : CollatzResearch.WordTrace tailWord_398428 prefixEnd_398428 68195023403224127439223 := by
  unfold tailWord_398428
  simp only [CollatzResearch.WordTrace]
  refine ⟨7265931500285438465041969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9687908667047251286722625 7265931500285438465041969)
  ·
    refine ⟨5449448625214078848781477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7265931500285438465041969 5449448625214078848781477)
    ·
      refine ⟨1021771617227639784146527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5449448625214078848781477 1021771617227639784146527)
      ·
        refine ⟨1532657425841459676219791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1021771617227639784146527 1532657425841459676219791)
        ·
          refine ⟨2298986138762189514329687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1532657425841459676219791 2298986138762189514329687)
          ·
            refine ⟨3448479208143284271494531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2298986138762189514329687 3448479208143284271494531)
            ·
              refine ⟨5172718812214926407241797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3448479208143284271494531 5172718812214926407241797)
              ·
                refine ⟨969884777290298701357837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5172718812214926407241797 969884777290298701357837)
                ·
                  refine ⟨363706791483862013009189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 969884777290298701357837 363706791483862013009189)
                  ·
                    refine ⟨68195023403224127439223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 363706791483862013009189 68195023403224127439223)
                    ·
                      rfl

theorem cell23_398428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_398428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_398428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_398428 prefixEnd_398428 := by exact prefixLift 398428
  have htrace : WordTrace (prefixWord ++ tailWord_398428) baseStart_398428 baseEnd_398428 := by
    simpa [prefixWord, tailWord_398428, baseEnd_398428] using wordTrace_append hprefix tailTrace_398428
  have hstable : (prefixWord ++ tailWord_398428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398428).length < 2 ^ (prefixWord ++ tailWord_398428).sum := by decide
  have hdescent : baseEnd_398428 < baseStart_398428 := by decide
  rcases family_descends (prefixWord ++ tailWord_398428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398471 : List Nat := [1, 1, 4, 2, 1, 1, 1, 4, 3, 5]
def baseStart_398471 : Nat := 118140960795 + 398471 * 2 ^ 59
def prefixEnd_398471 : Nat := 4983230072969 + 3 ^ 40 * 398471 * 2
def baseEnd_398471 : Nat := 68202383292605238026657

theorem tailTrace_398471 : CollatzResearch.WordTrace tailWord_398471 prefixEnd_398471 68202383292605238026657 := by
  unfold tailWord_398471
  simp only [CollatzResearch.WordTrace]
  refine ⟨14533431339415095273899267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9688954226276730182599511 14533431339415095273899267)
  ·
    refine ⟨21800147009122642910848901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14533431339415095273899267 21800147009122642910848901)
    ·
      refine ⟨4087527564210495545784169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21800147009122642910848901 4087527564210495545784169)
      ·
        refine ⟨3065645673157871659338127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4087527564210495545784169 3065645673157871659338127)
        ·
          refine ⟨4598468509736807489007191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3065645673157871659338127 4598468509736807489007191)
          ·
            refine ⟨6897702764605211233510787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4598468509736807489007191 6897702764605211233510787)
            ·
              refine ⟨10346554146907816850266181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6897702764605211233510787 10346554146907816850266181)
              ·
                refine ⟨1939978902545215659424909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10346554146907816850266181 1939978902545215659424909)
                ·
                  refine ⟨727492088454455872284341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1939978902545215659424909 727492088454455872284341)
                  ·
                    refine ⟨68202383292605238026657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 727492088454455872284341 68202383292605238026657)
                    ·
                      rfl

theorem cell23_398471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_398471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_398471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_398471 prefixEnd_398471 := by exact prefixLift 398471
  have htrace : WordTrace (prefixWord ++ tailWord_398471) baseStart_398471 baseEnd_398471 := by
    simpa [prefixWord, tailWord_398471, baseEnd_398471] using wordTrace_append hprefix tailTrace_398471
  have hstable : (prefixWord ++ tailWord_398471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398471).length < 2 ^ (prefixWord ++ tailWord_398471).sum := by decide
  have hdescent : baseEnd_398471 < baseStart_398471 := by decide
  rcases family_descends (prefixWord ++ tailWord_398471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398488 : List Nat := [2, 1, 2, 4, 2, 2, 1, 1, 3, 5]
def baseStart_398488 : Nat := 118140960795 + 398488 * 2 ^ 59
def prefixEnd_398488 : Nat := 4983230072969 + 3 ^ 40 * 398488 * 2
def baseEnd_398488 : Nat := 68205293016314049189131

theorem tailTrace_398488 : CollatzResearch.WordTrace tailWord_398488 prefixEnd_398488 68205293016314049189131 := by
  unfold tailWord_398488
  simp only [CollatzResearch.WordTrace]
  refine ⟨7267025690176753588634059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9689367586902338118178745 7267025690176753588634059)
  ·
    refine ⟨10900538535265130382951089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7267025690176753588634059 10900538535265130382951089)
    ·
      refine ⟨8175403901448847787213317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10900538535265130382951089 8175403901448847787213317)
      ·
        refine ⟨1532888231521658960102497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8175403901448847787213317 1532888231521658960102497)
        ·
          refine ⟨1149666173641244220076873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1532888231521658960102497 1149666173641244220076873)
          ·
            refine ⟨862249630230933165057655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1149666173641244220076873 862249630230933165057655)
            ·
              refine ⟨1293374445346399747586483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 862249630230933165057655 1293374445346399747586483)
              ·
                refine ⟨1940061668019599621379725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1293374445346399747586483 1940061668019599621379725)
                ·
                  refine ⟨727523125507349858017397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1940061668019599621379725 727523125507349858017397)
                  ·
                    refine ⟨68205293016314049189131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 727523125507349858017397 68205293016314049189131)
                    ·
                      rfl

theorem cell23_398488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 3, 5].length) (baseStart_398488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_398488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_398488 prefixEnd_398488 := by exact prefixLift 398488
  have htrace : WordTrace (prefixWord ++ tailWord_398488) baseStart_398488 baseEnd_398488 := by
    simpa [prefixWord, tailWord_398488, baseEnd_398488] using wordTrace_append hprefix tailTrace_398488
  have hstable : (prefixWord ++ tailWord_398488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398488).length < 2 ^ (prefixWord ++ tailWord_398488).sum := by decide
  have hdescent : baseEnd_398488 < baseStart_398488 := by decide
  rcases family_descends (prefixWord ++ tailWord_398488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398501 : List Nat := [1, 3, 1, 2, 1, 4, 1, 1, 3, 6]
def baseStart_398501 : Nat := 118140960795 + 398501 * 2 ^ 59
def prefixEnd_398501 : Nat := 4983230072969 + 3 ^ 40 * 398501 * 2
def baseEnd_398501 : Nat := 68207518099150198901611

theorem tailTrace_398501 : CollatzResearch.WordTrace tailWord_398501 prefixEnd_398501 68207518099150198901611 := by
  unfold tailWord_398501
  simp only [CollatzResearch.WordTrace]
  refine ⟨14534525529306410397491357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9689683686204273598327571 14534525529306410397491357)
  ·
    refine ⟨5450447073489903899059259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14534525529306410397491357 5450447073489903899059259)
    ·
      refine ⟨8175670610234855848588889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5450447073489903899059259 8175670610234855848588889)
      ·
        refine ⟨6131752957676141886441667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8175670610234855848588889 6131752957676141886441667)
        ·
          refine ⟨9197629436514212829662501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6131752957676141886441667 9197629436514212829662501)
          ·
            refine ⟨1724555519346414905561719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9197629436514212829662501 1724555519346414905561719)
            ·
              refine ⟨2586833279019622358342579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1724555519346414905561719 2586833279019622358342579)
              ·
                refine ⟨3880249918529433537513869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2586833279019622358342579 3880249918529433537513869)
                ·
                  refine ⟨1455093719448537576567701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3880249918529433537513869 1455093719448537576567701)
                  ·
                    refine ⟨68207518099150198901611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1455093719448537576567701 68207518099150198901611)
                    ·
                      rfl

theorem cell23_398501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 6].length) (baseStart_398501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_398501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_398501 prefixEnd_398501 := by exact prefixLift 398501
  have htrace : WordTrace (prefixWord ++ tailWord_398501) baseStart_398501 baseEnd_398501 := by
    simpa [prefixWord, tailWord_398501, baseEnd_398501] using wordTrace_append hprefix tailTrace_398501
  have hstable : (prefixWord ++ tailWord_398501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398501).length < 2 ^ (prefixWord ++ tailWord_398501).sum := by decide
  have hdescent : baseEnd_398501 < baseStart_398501 := by decide
  rcases family_descends (prefixWord ++ tailWord_398501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398538 : List Nat := [3, 1, 2, 1, 3, 2, 1, 3, 1, 2, 4]
def baseStart_398538 : Nat := 118140960795 + 398538 * 2 ^ 59
def prefixEnd_398538 : Nat := 4983230072969 + 3 ^ 40 * 398538 * 2
def baseEnd_398538 : Nat := 204641553081666951942163

theorem tailTrace_398538 : CollatzResearch.WordTrace tailWord_398538 prefixEnd_398538 204641553081666951942163 := by
  unfold tailWord_398538
  simp only [CollatzResearch.WordTrace]
  refine ⟨3633968757543091429147067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9690583353448243811058845 3633968757543091429147067)
  ·
    refine ⟨5450953136314637143720601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3633968757543091429147067 5450953136314637143720601)
    ·
      refine ⟨4088214852235977857790451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5450953136314637143720601 4088214852235977857790451)
      ·
        refine ⟨6132322278353966786685677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4088214852235977857790451 6132322278353966786685677)
        ·
          refine ⟨2299620854382737545007129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6132322278353966786685677 2299620854382737545007129)
          ·
            refine ⟨1724715640787053158755347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2299620854382737545007129 1724715640787053158755347)
            ·
              refine ⟨2587073461180579738133021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1724715640787053158755347 2587073461180579738133021)
              ·
                refine ⟨970152547942717401799883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2587073461180579738133021 970152547942717401799883)
                ·
                  refine ⟨1455228821914076102699825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 970152547942717401799883 1455228821914076102699825)
                  ·
                    refine ⟨1091421616435557077024869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1455228821914076102699825 1091421616435557077024869)
                    ·
                      refine ⟨204641553081666951942163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1091421616435557077024869 204641553081666951942163)
                      ·
                        rfl

theorem cell23_398538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_398538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_398538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_398538 prefixEnd_398538 := by exact prefixLift 398538
  have htrace : WordTrace (prefixWord ++ tailWord_398538) baseStart_398538 baseEnd_398538 := by
    simpa [prefixWord, tailWord_398538, baseEnd_398538] using wordTrace_append hprefix tailTrace_398538
  have hstable : (prefixWord ++ tailWord_398538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398538).length < 2 ^ (prefixWord ++ tailWord_398538).sum := by decide
  have hdescent : baseEnd_398538 < baseStart_398538 := by decide
  rcases family_descends (prefixWord ++ tailWord_398538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398610 : List Nat := [3, 2, 4, 2, 1, 2, 1, 3, 1, 2, 2]
def baseStart_398610 : Nat := 118140960795 + 398610 * 2 ^ 59
def prefixEnd_398610 : Nat := 4983230072969 + 3 ^ 40 * 398610 * 2
def baseEnd_398610 : Nat := 204678523688790670241833

theorem tailTrace_398610 : CollatzResearch.WordTrace tailWord_398610 prefixEnd_398610 204678523688790670241833 := by
  unfold tailWord_398610
  simp only [CollatzResearch.WordTrace]
  refine ⟨3634625271477880503302321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9692334057274348008806189 3634625271477880503302321)
  ·
    refine ⟨2725968953608410377476741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3634625271477880503302321 2725968953608410377476741)
    ·
      refine ⟨511119178801576945776889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2725968953608410377476741 511119178801576945776889)
      ·
        refine ⟨383339384101182709332667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 511119178801576945776889 383339384101182709332667)
        ·
          refine ⟨575009076151774063999001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383339384101182709332667 575009076151774063999001)
          ·
            refine ⟨431256807113830547999251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 575009076151774063999001 431256807113830547999251)
            ·
              refine ⟨646885210670745821998877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 431256807113830547999251 646885210670745821998877)
              ·
                refine ⟨242581954001529683249579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 646885210670745821998877 242581954001529683249579)
                ·
                  refine ⟨363872931002294524874369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 242581954001529683249579 363872931002294524874369)
                  ·
                    refine ⟨272904698251720893655777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 363872931002294524874369 272904698251720893655777)
                    ·
                      refine ⟨204678523688790670241833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 272904698251720893655777 204678523688790670241833)
                      ·
                        rfl

theorem cell23_398610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_398610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_398610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_398610 prefixEnd_398610 := by exact prefixLift 398610
  have htrace : WordTrace (prefixWord ++ tailWord_398610) baseStart_398610 baseEnd_398610 := by
    simpa [prefixWord, tailWord_398610, baseEnd_398610] using wordTrace_append hprefix tailTrace_398610
  have hstable : (prefixWord ++ tailWord_398610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398610).length < 2 ^ (prefixWord ++ tailWord_398610).sum := by decide
  have hdescent : baseEnd_398610 < baseStart_398610 := by decide
  rcases family_descends (prefixWord ++ tailWord_398610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398615 : List Nat := [1, 1, 3, 4, 1, 1, 2, 1, 3, 4, 2]
def baseStart_398615 : Nat := 118140960795 + 398615 * 2 ^ 59
def prefixEnd_398615 : Nat := 4983230072969 + 3 ^ 40 * 398615 * 2
def baseEnd_398615 : Nat := 204681091092063150679309

theorem tailTrace_398615 : CollatzResearch.WordTrace tailWord_398615 prefixEnd_398615 204681091092063150679309 := by
  unfold tailWord_398615
  simp only [CollatzResearch.WordTrace]
  refine ⟨14538683450893407867141299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9692455633928938578094199 14538683450893407867141299)
  ·
    refine ⟨21808025176340111800711949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14538683450893407867141299 21808025176340111800711949)
    ·
      refine ⟨8178009441127541925266981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21808025176340111800711949 8178009441127541925266981)
      ·
        refine ⟨1533376770211414110987559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8178009441127541925266981 1533376770211414110987559)
        ·
          refine ⟨2300065155317121166481339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1533376770211414110987559 2300065155317121166481339)
          ·
            refine ⟨3450097732975681749722009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2300065155317121166481339 3450097732975681749722009)
            ·
              refine ⟨2587573299731761312291507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3450097732975681749722009 2587573299731761312291507)
              ·
                refine ⟨3881359949597641968437261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2587573299731761312291507 3881359949597641968437261)
                ·
                  refine ⟨1455509981099115738163973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3881359949597641968437261 1455509981099115738163973)
                  ·
                    refine ⟨272908121456084200905745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1455509981099115738163973 272908121456084200905745)
                    ·
                      refine ⟨204681091092063150679309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 272908121456084200905745 204681091092063150679309)
                      ·
                        rfl

theorem cell23_398615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_398615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_398615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_398615 prefixEnd_398615 := by exact prefixLift 398615
  have htrace : WordTrace (prefixWord ++ tailWord_398615) baseStart_398615 baseEnd_398615 := by
    simpa [prefixWord, tailWord_398615, baseEnd_398615] using wordTrace_append hprefix tailTrace_398615
  have hstable : (prefixWord ++ tailWord_398615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398615).length < 2 ^ (prefixWord ++ tailWord_398615).sum := by decide
  have hdescent : baseEnd_398615 < baseStart_398615 := by decide
  rcases family_descends (prefixWord ++ tailWord_398615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398618 : List Nat := [3, 1, 1, 3, 3, 1, 1, 1, 1, 3, 5]
def baseStart_398618 : Nat := 118140960795 + 398618 * 2 ^ 59
def prefixEnd_398618 : Nat := 4983230072969 + 3 ^ 40 * 398618 * 2
def baseEnd_398618 : Nat := 204682631534026638941795

theorem tailTrace_398618 : CollatzResearch.WordTrace tailWord_398618 prefixEnd_398618 204682631534026638941795 := by
  unfold tailWord_398618
  simp only [CollatzResearch.WordTrace]
  refine ⟨3634698217470634844875127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9692528579921692919667005 3634698217470634844875127)
  ·
    refine ⟨5452047326205952267312691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3634698217470634844875127 5452047326205952267312691)
    ·
      refine ⟨8178070989308928400969037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5452047326205952267312691 8178070989308928400969037)
      ·
        refine ⟨3066776620990848150363389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8178070989308928400969037 3066776620990848150363389)
        ·
          refine ⟨1150041232871568056386271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3066776620990848150363389 1150041232871568056386271)
          ·
            refine ⟨1725061849307352084579407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1150041232871568056386271 1725061849307352084579407)
            ·
              refine ⟨2587592773961028126869111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1725061849307352084579407 2587592773961028126869111)
              ·
                refine ⟨3881389160941542190303667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2587592773961028126869111 3881389160941542190303667)
                ·
                  refine ⟨5822083741412313285455501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3881389160941542190303667 5822083741412313285455501)
                  ·
                    refine ⟨2183281403029617482045813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5822083741412313285455501 2183281403029617482045813)
                    ·
                      refine ⟨204682631534026638941795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2183281403029617482045813 204682631534026638941795)
                      ·
                        rfl

theorem cell23_398618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_398618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_398618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_398618 prefixEnd_398618 := by exact prefixLift 398618
  have htrace : WordTrace (prefixWord ++ tailWord_398618) baseStart_398618 baseEnd_398618 := by
    simpa [prefixWord, tailWord_398618, baseEnd_398618] using wordTrace_append hprefix tailTrace_398618
  have hstable : (prefixWord ++ tailWord_398618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398618).length < 2 ^ (prefixWord ++ tailWord_398618).sum := by decide
  have hdescent : baseEnd_398618 < baseStart_398618 := by decide
  rcases family_descends (prefixWord ++ tailWord_398618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398648 : List Nat := [2, 1, 2, 1, 3, 1, 1, 3, 1, 5, 3]
def baseStart_398648 : Nat := 118140960795 + 398648 * 2 ^ 59
def prefixEnd_398648 : Nat := 4983230072969 + 3 ^ 40 * 398648 * 2
def baseEnd_398648 : Nat := 204698035953661521566657

theorem tailTrace_398648 : CollatzResearch.WordTrace tailWord_398648 prefixEnd_398648 204698035953661521566657 := by
  unfold tailWord_398648
  simp only [CollatzResearch.WordTrace]
  refine ⟨7269943529886927251546299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9693258039849236335395065 7269943529886927251546299)
  ·
    refine ⟨10904915294830390877319449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7269943529886927251546299 10904915294830390877319449)
    ·
      refine ⟨8178686471122793157989587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10904915294830390877319449 8178686471122793157989587)
      ·
        refine ⟨12268029706684189736984381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8178686471122793157989587 12268029706684189736984381)
        ·
          refine ⟨4600511140006571151369143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12268029706684189736984381 4600511140006571151369143)
          ·
            refine ⟨6900766710009856727053715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4600511140006571151369143 6900766710009856727053715)
            ·
              refine ⟨10351150065014785090580573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6900766710009856727053715 10351150065014785090580573)
              ·
                refine ⟨3881681274380544408967715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10351150065014785090580573 3881681274380544408967715)
                ·
                  refine ⟨5822521911570816613451573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3881681274380544408967715 5822521911570816613451573)
                  ·
                    refine ⟨545861429209764057511085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5822521911570816613451573 545861429209764057511085)
                    ·
                      refine ⟨204698035953661521566657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 545861429209764057511085 204698035953661521566657)
                      ·
                        rfl

theorem cell23_398648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 1, 5, 3].length) (baseStart_398648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_398648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_398648 prefixEnd_398648 := by exact prefixLift 398648
  have htrace : WordTrace (prefixWord ++ tailWord_398648) baseStart_398648 baseEnd_398648 := by
    simpa [prefixWord, tailWord_398648, baseEnd_398648] using wordTrace_append hprefix tailTrace_398648
  have hstable : (prefixWord ++ tailWord_398648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398648).length < 2 ^ (prefixWord ++ tailWord_398648).sum := by decide
  have hdescent : baseEnd_398648 < baseStart_398648 := by decide
  rcases family_descends (prefixWord ++ tailWord_398648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398653 : List Nat := [1, 4, 1, 5, 2, 1, 1, 2, 1, 3, 2]
def baseStart_398653 : Nat := 118140960795 + 398653 * 2 ^ 59
def prefixEnd_398653 : Nat := 4983230072969 + 3 ^ 40 * 398653 * 2
def baseEnd_398653 : Nat := 204700603356934002004135

theorem tailTrace_398653 : CollatzResearch.WordTrace tailWord_398653 prefixEnd_398653 204700603356934002004135 := by
  unfold tailWord_398653
  simp only [CollatzResearch.WordTrace]
  refine ⟨14540069424755740357024613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9693379616503826904683075 14540069424755740357024613)
  ·
    refine ⟨2726263017141701316942115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14540069424755740357024613 2726263017141701316942115)
    ·
      refine ⟨4089394525712551975413173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2726263017141701316942115 4089394525712551975413173)
      ·
        refine ⟨383380736785551747694985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4089394525712551975413173 383380736785551747694985)
        ·
          refine ⟨287535552589163810771239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 383380736785551747694985 287535552589163810771239)
          ·
            refine ⟨431303328883745716156859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287535552589163810771239 431303328883745716156859)
            ·
              refine ⟨646954993325618574235289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 431303328883745716156859 646954993325618574235289)
              ·
                refine ⟨485216244994213930676467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 646954993325618574235289 485216244994213930676467)
                ·
                  refine ⟨727824367491320896014701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 485216244994213930676467 727824367491320896014701)
                  ·
                    refine ⟨272934137809245336005513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 727824367491320896014701 272934137809245336005513)
                    ·
                      refine ⟨204700603356934002004135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 272934137809245336005513 204700603356934002004135)
                      ·
                        rfl

theorem cell23_398653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_398653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_398653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_398653 prefixEnd_398653 := by exact prefixLift 398653
  have htrace : WordTrace (prefixWord ++ tailWord_398653) baseStart_398653 baseEnd_398653 := by
    simpa [prefixWord, tailWord_398653, baseEnd_398653] using wordTrace_append hprefix tailTrace_398653
  have hstable : (prefixWord ++ tailWord_398653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398653).length < 2 ^ (prefixWord ++ tailWord_398653).sum := by decide
  have hdescent : baseEnd_398653 < baseStart_398653 := by decide
  rcases family_descends (prefixWord ++ tailWord_398653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398705 : List Nat := [1, 2, 2, 2, 1, 2, 3, 1, 1, 6, 2]
def baseStart_398705 : Nat := 118140960795 + 398705 * 2 ^ 59
def prefixEnd_398705 : Nat := 4983230072969 + 3 ^ 40 * 398705 * 2
def baseEnd_398705 : Nat := 204727304350967798553895

theorem tailTrace_398705 : CollatzResearch.WordTrace tailWord_398705 prefixEnd_398705 204727304350967798553895 := by
  unfold tailWord_398705
  simp only [CollatzResearch.WordTrace]
  refine ⟨14541966020567353237917569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9694644013711568825278379 14541966020567353237917569)
  ·
    refine ⟨10906474515425514928438177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14541966020567353237917569 10906474515425514928438177)
    ·
      refine ⟨8179855886569136196328633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10906474515425514928438177 8179855886569136196328633)
      ·
        refine ⟨6134891914926852147246475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8179855886569136196328633 6134891914926852147246475)
        ·
          refine ⟨9202337872390278220869713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6134891914926852147246475 9202337872390278220869713)
          ·
            refine ⟨6901753404292708665652285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9202337872390278220869713 6901753404292708665652285)
            ·
              refine ⟨2588157526609765749619607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6901753404292708665652285 2588157526609765749619607)
              ·
                refine ⟨3882236289914648624429411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2588157526609765749619607 3882236289914648624429411)
                ·
                  refine ⟨5823354434871972936644117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3882236289914648624429411 5823354434871972936644117)
                  ·
                    refine ⟨272969739134623731405193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5823354434871972936644117 272969739134623731405193)
                    ·
                      refine ⟨204727304350967798553895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 272969739134623731405193 204727304350967798553895)
                      ·
                        rfl

theorem cell23_398705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 6, 2].length) (baseStart_398705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_398705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_398705 prefixEnd_398705 := by exact prefixLift 398705
  have htrace : WordTrace (prefixWord ++ tailWord_398705) baseStart_398705 baseEnd_398705 := by
    simpa [prefixWord, tailWord_398705, baseEnd_398705] using wordTrace_append hprefix tailTrace_398705
  have hstable : (prefixWord ++ tailWord_398705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398705).length < 2 ^ (prefixWord ++ tailWord_398705).sum := by decide
  have hdescent : baseEnd_398705 < baseStart_398705 := by decide
  rcases family_descends (prefixWord ++ tailWord_398705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398715 : List Nat := [1, 1, 1, 1, 1, 6, 3, 2, 3, 4]
def baseStart_398715 : Nat := 118140960795 + 398715 * 2 ^ 59
def prefixEnd_398715 : Nat := 4983230072969 + 3 ^ 40 * 398715 * 2
def baseEnd_398715 : Nat := 68244146385837586476283

theorem tailTrace_398715 : CollatzResearch.WordTrace tailWord_398715 prefixEnd_398715 68244146385837586476283 := by
  unfold tailWord_398715
  simp only [CollatzResearch.WordTrace]
  refine ⟨14542330750531124945781599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9694887167020749963854399 14542330750531124945781599)
  ·
    refine ⟨21813496125796687418672399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14542330750531124945781599 21813496125796687418672399)
    ·
      refine ⟨32720244188695031128008599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21813496125796687418672399 32720244188695031128008599)
      ·
        refine ⟨49080366283042546692012899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32720244188695031128008599 49080366283042546692012899)
        ·
          refine ⟨73620549424563820038019349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49080366283042546692012899 73620549424563820038019349)
          ·
            refine ⟨3450963254276429064282157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 73620549424563820038019349 3450963254276429064282157)
            ·
              refine ⟨1294111220353660899105809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3450963254276429064282157 1294111220353660899105809)
              ·
                refine ⟨970583415265245674329357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1294111220353660899105809 970583415265245674329357)
                ·
                  refine ⟨363968780724467127873509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 970583415265245674329357 363968780724467127873509)
                  ·
                    refine ⟨68244146385837586476283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 363968780724467127873509 68244146385837586476283)
                    ·
                      rfl

theorem cell23_398715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 3, 4].length) (baseStart_398715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_398715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_398715 prefixEnd_398715 := by exact prefixLift 398715
  have htrace : WordTrace (prefixWord ++ tailWord_398715) baseStart_398715 baseEnd_398715 := by
    simpa [prefixWord, tailWord_398715, baseEnd_398715] using wordTrace_append hprefix tailTrace_398715
  have hstable : (prefixWord ++ tailWord_398715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398715).length < 2 ^ (prefixWord ++ tailWord_398715).sum := by decide
  have hdescent : baseEnd_398715 < baseStart_398715 := by decide
  rcases family_descends (prefixWord ++ tailWord_398715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398745 : List Nat := [1, 2, 1, 2, 1, 5, 3, 2, 6]
def baseStart_398745 : Nat := 118140960795 + 398745 * 2 ^ 59
def prefixEnd_398745 : Nat := 4983230072969 + 3 ^ 40 * 398745 * 2
def baseEnd_398745 : Nat := 22749760397460849117079

theorem tailTrace_398745 : CollatzResearch.WordTrace tailWord_398745 prefixEnd_398745 22749760397460849117079 := by
  unfold tailWord_398745
  simp only [CollatzResearch.WordTrace]
  refine ⟨14543424940422440069373689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9695616626948293379582459 14543424940422440069373689)
  ·
    refine ⟨10907568705316830052030267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14543424940422440069373689 10907568705316830052030267)
    ·
      refine ⟨16361353057975245078045401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10907568705316830052030267 16361353057975245078045401)
      ·
        refine ⟨12271014793481433808534051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16361353057975245078045401 12271014793481433808534051)
        ·
          refine ⟨18406522190222150712801077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12271014793481433808534051 18406522190222150712801077)
          ·
            refine ⟨1725611455333326629325101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18406522190222150712801077 1725611455333326629325101)
            ·
              refine ⟨647104295749997485996913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1725611455333326629325101 647104295749997485996913)
              ·
                refine ⟨485328221812498114497685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 647104295749997485996913 485328221812498114497685)
                ·
                  refine ⟨22749760397460849117079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 485328221812498114497685 22749760397460849117079)
                  ·
                    rfl

theorem cell23_398745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2, 6].length) (baseStart_398745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_398745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_398745 prefixEnd_398745 := by exact prefixLift 398745
  have htrace : WordTrace (prefixWord ++ tailWord_398745) baseStart_398745 baseEnd_398745 := by
    simpa [prefixWord, tailWord_398745, baseEnd_398745] using wordTrace_append hprefix tailTrace_398745
  have hstable : (prefixWord ++ tailWord_398745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398745).length < 2 ^ (prefixWord ++ tailWord_398745).sum := by decide
  have hdescent : baseEnd_398745 < baseStart_398745 := by decide
  rcases family_descends (prefixWord ++ tailWord_398745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398749 : List Nat := [1, 4, 2, 1, 3, 1, 2, 4, 1, 4]
def baseStart_398749 : Nat := 118140960795 + 398749 * 2 ^ 59
def prefixEnd_398749 : Nat := 4983230072969 + 3 ^ 40 * 398749 * 2
def baseEnd_398749 : Nat := 68249965833255208801231

theorem tailTrace_398749 : CollatzResearch.WordTrace tailWord_398749 prefixEnd_398749 68249965833255208801231 := by
  unfold tailWord_398749
  simp only [CollatzResearch.WordTrace]
  refine ⟨14543570832407948752519301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9695713888271965835012867 14543570832407948752519301)
  ·
    refine ⟨2726919531076490391097369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14543570832407948752519301 2726919531076490391097369)
    ·
      refine ⟨2045189648307367793323027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2726919531076490391097369 2045189648307367793323027)
      ·
        refine ⟨3067784472461051689984541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2045189648307367793323027 3067784472461051689984541)
        ·
          refine ⟨1150419177172894383744203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3067784472461051689984541 1150419177172894383744203)
          ·
            refine ⟨1725628765759341575616305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1150419177172894383744203 1725628765759341575616305)
            ·
              refine ⟨1294221574319506181712229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1725628765759341575616305 1294221574319506181712229)
              ·
                refine ⟨242666545184907409071043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1294221574319506181712229 242666545184907409071043)
                ·
                  refine ⟨363999817777361113606565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 242666545184907409071043 363999817777361113606565)
                  ·
                    refine ⟨68249965833255208801231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 363999817777361113606565 68249965833255208801231)
                    ·
                      rfl

theorem cell23_398749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_398749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_398749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_398749 prefixEnd_398749 := by exact prefixLift 398749
  have htrace : WordTrace (prefixWord ++ tailWord_398749) baseStart_398749 baseEnd_398749 := by
    simpa [prefixWord, tailWord_398749, baseEnd_398749] using wordTrace_append hprefix tailTrace_398749
  have hstable : (prefixWord ++ tailWord_398749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398749).length < 2 ^ (prefixWord ++ tailWord_398749).sum := by decide
  have hdescent : baseEnd_398749 < baseStart_398749 := by decide
  rcases family_descends (prefixWord ++ tailWord_398749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398806 : List Nat := [5, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3]
def baseStart_398806 : Nat := 118140960795 + 398806 * 2 ^ 59
def prefixEnd_398806 : Nat := 4983230072969 + 3 ^ 40 * 398806 * 2
def baseEnd_398806 : Nat := 204779165897071903390931

theorem tailTrace_398806 : CollatzResearch.WordTrace tailWord_398806 prefixEnd_398806 204779165897071903390931 := by
  unfold tailWord_398806
  simp only [CollatzResearch.WordTrace]
  refine ⟨909103112075090467959017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9697099862134298324896181 909103112075090467959017)
  ·
    refine ⟨681827334056317850969263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 909103112075090467959017 681827334056317850969263)
    ·
      refine ⟨1022741001084476776453895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 681827334056317850969263 1022741001084476776453895)
      ·
        refine ⟨1534111501626715164680843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1022741001084476776453895 1534111501626715164680843)
        ·
          refine ⟨2301167252440072747021265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1534111501626715164680843 2301167252440072747021265)
          ·
            refine ⟨1725875439330054560265949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2301167252440072747021265 1725875439330054560265949)
            ·
              refine ⟨647203289748770460099731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1725875439330054560265949 647203289748770460099731)
              ·
                refine ⟨970804934623155690149597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 647203289748770460099731 970804934623155690149597)
                ·
                  refine ⟨364051850483683383806099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 970804934623155690149597 364051850483683383806099)
                  ·
                    refine ⟨546077775725525075709149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 364051850483683383806099 546077775725525075709149)
                    ·
                      refine ⟨204779165897071903390931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 546077775725525075709149 204779165897071903390931)
                      ·
                        rfl

theorem cell23_398806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_398806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_398806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_398806 prefixEnd_398806 := by exact prefixLift 398806
  have htrace : WordTrace (prefixWord ++ tailWord_398806) baseStart_398806 baseEnd_398806 := by
    simpa [prefixWord, tailWord_398806, baseEnd_398806] using wordTrace_append hprefix tailTrace_398806
  have hstable : (prefixWord ++ tailWord_398806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398806).length < 2 ^ (prefixWord ++ tailWord_398806).sum := by decide
  have hdescent : baseEnd_398806 < baseStart_398806 := by decide
  rcases family_descends (prefixWord ++ tailWord_398806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398815 : List Nat := [1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 5]
def baseStart_398815 : Nat := 118140960795 + 398815 * 2 ^ 59
def prefixEnd_398815 : Nat := 4983230072969 + 3 ^ 40 * 398815 * 2
def baseEnd_398815 : Nat := 204783787222962368178389

theorem tailTrace_398815 : CollatzResearch.WordTrace tailWord_398815 prefixEnd_398815 204783787222962368178389 := by
  unfold tailWord_398815
  simp only [CollatzResearch.WordTrace]
  refine ⟨14545978050168842024421899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9697318700112561349614599 14545978050168842024421899)
  ·
    refine ⟨21818967075253263036632849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14545978050168842024421899 21818967075253263036632849)
    ·
      refine ⟨16364225306439947277474637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21818967075253263036632849 16364225306439947277474637)
      ·
        refine ⟨6136584489914980229052989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16364225306439947277474637 6136584489914980229052989)
        ·
          refine ⟨2301219183718117585894871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6136584489914980229052989 2301219183718117585894871)
          ·
            refine ⟨3451828775577176378842307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2301219183718117585894871 3451828775577176378842307)
            ·
              refine ⟨5177743163365764568263461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3451828775577176378842307 5177743163365764568263461)
              ·
                refine ⟨970826843131080856549399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5177743163365764568263461 970826843131080856549399)
                ·
                  refine ⟨1456240264696621284824099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 970826843131080856549399 1456240264696621284824099)
                  ·
                    refine ⟨2184360397044931927236149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1456240264696621284824099 2184360397044931927236149)
                    ·
                      refine ⟨204783787222962368178389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2184360397044931927236149 204783787222962368178389)
                      ·
                        rfl

theorem cell23_398815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_398815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_398815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_398815 prefixEnd_398815 := by exact prefixLift 398815
  have htrace : WordTrace (prefixWord ++ tailWord_398815) baseStart_398815 baseEnd_398815 := by
    simpa [prefixWord, tailWord_398815, baseEnd_398815] using wordTrace_append hprefix tailTrace_398815
  have hstable : (prefixWord ++ tailWord_398815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398815).length < 2 ^ (prefixWord ++ tailWord_398815).sum := by decide
  have hdescent : baseEnd_398815 < baseStart_398815 := by decide
  rcases family_descends (prefixWord ++ tailWord_398815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398826 : List Nat := [3, 1, 3, 1, 5, 1, 1, 2, 1, 5]
def baseStart_398826 : Nat := 118140960795 + 398826 * 2 ^ 59
def prefixEnd_398826 : Nat := 4983230072969 + 3 ^ 40 * 398826 * 2
def baseEnd_398826 : Nat := 68263145170053941713613

theorem tailTrace_398826 : CollatzResearch.WordTrace tailWord_398826 prefixEnd_398826 68263145170053941713613 := by
  unfold tailWord_398826
  simp only [CollatzResearch.WordTrace]
  refine ⟨3636594813282247725768083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9697586168752660602048221 3636594813282247725768083)
  ·
    refine ⟨5454892219923371588652125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3636594813282247725768083 5454892219923371588652125)
    ·
      refine ⟨2045584582471264345744547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5454892219923371588652125 2045584582471264345744547)
      ·
        refine ⟨3068376873706896518616821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2045584582471264345744547 3068376873706896518616821)
        ·
          refine ⟨287660331910021548620327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3068376873706896518616821 287660331910021548620327)
          ·
            refine ⟨431490497865032322930491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287660331910021548620327 431490497865032322930491)
            ·
              refine ⟨647235746797548484395737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 431490497865032322930491 647235746797548484395737)
              ·
                refine ⟨485426810098161363296803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 647235746797548484395737 485426810098161363296803)
                ·
                  refine ⟨728140215147242044945205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 485426810098161363296803 728140215147242044945205)
                  ·
                    refine ⟨68263145170053941713613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 728140215147242044945205 68263145170053941713613)
                    ·
                      rfl

theorem cell23_398826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_398826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_398826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_398826 prefixEnd_398826 := by exact prefixLift 398826
  have htrace : WordTrace (prefixWord ++ tailWord_398826) baseStart_398826 baseEnd_398826 := by
    simpa [prefixWord, tailWord_398826, baseEnd_398826] using wordTrace_append hprefix tailTrace_398826
  have hstable : (prefixWord ++ tailWord_398826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398826).length < 2 ^ (prefixWord ++ tailWord_398826).sum := by decide
  have hdescent : baseEnd_398826 < baseStart_398826 := by decide
  rcases family_descends (prefixWord ++ tailWord_398826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398829 : List Nat := [1, 5, 1, 3, 2, 1, 1, 1, 3, 1, 4]
def baseStart_398829 : Nat := 118140960795 + 398829 * 2 ^ 59
def prefixEnd_398829 : Nat := 4983230072969 + 3 ^ 40 * 398829 * 2
def baseEnd_398829 : Nat := 204790975952125313403325

theorem tailTrace_398829 : CollatzResearch.WordTrace tailWord_398829 prefixEnd_398829 204790975952125313403325 := by
  unfold tailWord_398829
  simp only [CollatzResearch.WordTrace]
  refine ⟨14546488672118122415431541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9697659114745414943621027 14546488672118122415431541)
  ·
    refine ⟨1363733313011073976446707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14546488672118122415431541 1363733313011073976446707)
    ·
      refine ⟨2045599969516610964670061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1363733313011073976446707 2045599969516610964670061)
      ·
        refine ⟨767099988568729111751273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2045599969516610964670061 767099988568729111751273)
        ·
          refine ⟨575324991426546833813455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 767099988568729111751273 575324991426546833813455)
          ·
            refine ⟨862987487139820250720183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 575324991426546833813455 862987487139820250720183)
            ·
              refine ⟨1294481230709730376080275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 862987487139820250720183 1294481230709730376080275)
              ·
                refine ⟨1941721846064595564120413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1294481230709730376080275 1941721846064595564120413)
                ·
                  refine ⟨728145692274223336545155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1941721846064595564120413 728145692274223336545155)
                  ·
                    refine ⟨1092218538411335004817733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 728145692274223336545155 1092218538411335004817733)
                    ·
                      refine ⟨204790975952125313403325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1092218538411335004817733 204790975952125313403325)
                      ·
                        rfl

theorem cell23_398829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_398829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_398829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_398829 prefixEnd_398829 := by exact prefixLift 398829
  have htrace : WordTrace (prefixWord ++ tailWord_398829) baseStart_398829 baseEnd_398829 := by
    simpa [prefixWord, tailWord_398829, baseEnd_398829] using wordTrace_append hprefix tailTrace_398829
  have hstable : (prefixWord ++ tailWord_398829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398829).length < 2 ^ (prefixWord ++ tailWord_398829).sum := by decide
  have hdescent : baseEnd_398829 < baseStart_398829 := by decide
  rcases family_descends (prefixWord ++ tailWord_398829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398832 : List Nat := [2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 3]
def baseStart_398832 : Nat := 118140960795 + 398832 * 2 ^ 59
def prefixEnd_398832 : Nat := 4983230072969 + 3 ^ 40 * 398832 * 2
def baseEnd_398832 : Nat := 204792516394088801665811

theorem tailTrace_398832 : CollatzResearch.WordTrace tailWord_398832 prefixEnd_398832 204792516394088801665811 := by
  unfold tailWord_398832
  simp only [CollatzResearch.WordTrace]
  refine ⟨7273299045553626963895375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9697732060738169285193833 7273299045553626963895375)
  ·
    refine ⟨10909948568330440445843063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7273299045553626963895375 10909948568330440445843063)
    ·
      refine ⟨16364922852495660668764595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10909948568330440445843063 16364922852495660668764595)
      ·
        refine ⟨24547384278743491003146893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16364922852495660668764595 24547384278743491003146893)
        ·
          refine ⟨9205269104528809126180085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24547384278743491003146893 9205269104528809126180085)
          ·
            refine ⟨862993978549575855579383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9205269104528809126180085 862993978549575855579383)
            ·
              refine ⟨1294490967824363783369075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 862993978549575855579383 1294490967824363783369075)
              ·
                refine ⟨1941736451736545675053613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1294490967824363783369075 1941736451736545675053613)
                ·
                  refine ⟨728151169401204628145105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1941736451736545675053613 728151169401204628145105)
                  ·
                    refine ⟨546113377050903471108829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 728151169401204628145105 546113377050903471108829)
                    ·
                      refine ⟨204792516394088801665811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 546113377050903471108829 204792516394088801665811)
                      ·
                        rfl

theorem cell23_398832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 3].length) (baseStart_398832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_398832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_398832 prefixEnd_398832 := by exact prefixLift 398832
  have htrace : WordTrace (prefixWord ++ tailWord_398832) baseStart_398832 baseEnd_398832 := by
    simpa [prefixWord, tailWord_398832, baseEnd_398832] using wordTrace_append hprefix tailTrace_398832
  have hstable : (prefixWord ++ tailWord_398832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398832).length < 2 ^ (prefixWord ++ tailWord_398832).sum := by decide
  have hdescent : baseEnd_398832 < baseStart_398832 := by decide
  rcases family_descends (prefixWord ++ tailWord_398832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398849 : List Nat := [1, 2, 4, 1, 4, 2, 1, 1, 1, 1, 5]
def baseStart_398849 : Nat := 118140960795 + 398849 * 2 ^ 59
def prefixEnd_398849 : Nat := 4983230072969 + 3 ^ 40 * 398849 * 2
def baseEnd_398849 : Nat := 204801245565215235153233

theorem tailTrace_398849 : CollatzResearch.WordTrace tailWord_398849 prefixEnd_398849 204801245565215235153233 := by
  unfold tailWord_398849
  simp only [CollatzResearch.WordTrace]
  refine ⟨14547218132045665831159601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9698145421363777220773067 14547218132045665831159601)
  ·
    refine ⟨10910413599034249373369701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14547218132045665831159601 10910413599034249373369701)
    ·
      refine ⟨2045702549818921757506819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10910413599034249373369701 2045702549818921757506819)
      ·
        refine ⟨3068553824728382636260229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2045702549818921757506819 3068553824728382636260229)
        ·
          refine ⟨575353842136571744298793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3068553824728382636260229 575353842136571744298793)
          ·
            refine ⟨431515381602428808224095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 575353842136571744298793 431515381602428808224095)
            ·
              refine ⟨647273072403643212336143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 431515381602428808224095 647273072403643212336143)
              ·
                refine ⟨970909608605464818504215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 647273072403643212336143 970909608605464818504215)
                ·
                  refine ⟨1456364412908197227756323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 970909608605464818504215 1456364412908197227756323)
                  ·
                    refine ⟨2184546619362295841634485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1456364412908197227756323 2184546619362295841634485)
                    ·
                      refine ⟨204801245565215235153233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2184546619362295841634485 204801245565215235153233)
                      ·
                        rfl

theorem cell23_398849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_398849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_398849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_398849 prefixEnd_398849 := by exact prefixLift 398849
  have htrace : WordTrace (prefixWord ++ tailWord_398849) baseStart_398849 baseEnd_398849 := by
    simpa [prefixWord, tailWord_398849, baseEnd_398849] using wordTrace_append hprefix tailTrace_398849
  have hstable : (prefixWord ++ tailWord_398849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398849).length < 2 ^ (prefixWord ++ tailWord_398849).sum := by decide
  have hdescent : baseEnd_398849 < baseStart_398849 := by decide
  rcases family_descends (prefixWord ++ tailWord_398849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398852 : List Nat := [2, 3, 2, 3, 3, 10]
def baseStart_398852 : Nat := 118140960795 + 398852 * 2 ^ 59
def prefixEnd_398852 : Nat := 4983230072969 + 3 ^ 40 * 398852 * 2
def baseEnd_398852 : Nat := 842809818959583223933

theorem tailTrace_398852 : CollatzResearch.WordTrace tailWord_398852 prefixEnd_398852 842809818959583223933 := by
  unfold tailWord_398852
  simp only [CollatzResearch.WordTrace]
  refine ⟨7273663775517398671759405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9698218367356531562345873 7273663775517398671759405)
  ·
    refine ⟨2727623915819024501909777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7273663775517398671759405 2727623915819024501909777)
    ·
      refine ⟨2045717936864268376432333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2727623915819024501909777 2045717936864268376432333)
      ·
        refine ⟨767144226324100641162125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2045717936864268376432333 767144226324100641162125)
        ·
          refine ⟨287679084871537740435797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 767144226324100641162125 287679084871537740435797)
          ·
            refine ⟨842809818959583223933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 287679084871537740435797 842809818959583223933)
            ·
              rfl

theorem cell23_398852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 10].length) (baseStart_398852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_398852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_398852 prefixEnd_398852 := by exact prefixLift 398852
  have htrace : WordTrace (prefixWord ++ tailWord_398852) baseStart_398852 baseEnd_398852 := by
    simpa [prefixWord, tailWord_398852, baseEnd_398852] using wordTrace_append hprefix tailTrace_398852
  have hstable : (prefixWord ++ tailWord_398852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398852).length < 2 ^ (prefixWord ++ tailWord_398852).sum := by decide
  have hdescent : baseEnd_398852 < baseStart_398852 := by decide
  rcases family_descends (prefixWord ++ tailWord_398852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398879 : List Nat := [1, 1, 2, 4, 1, 1, 4, 3, 2, 1, 3]
def baseStart_398879 : Nat := 118140960795 + 398879 * 2 ^ 59
def prefixEnd_398879 : Nat := 4983230072969 + 3 ^ 40 * 398879 * 2
def baseEnd_398879 : Nat := 204816649984850117778095

theorem tailTrace_398879 : CollatzResearch.WordTrace tailWord_398879 prefixEnd_398879 204816649984850117778095 := by
  unfold tailWord_398879
  simp only [CollatzResearch.WordTrace]
  refine ⟨14548312321936980954751691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9698874881291320636501127 14548312321936980954751691)
  ·
    refine ⟨21822468482905471432127537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14548312321936980954751691 21822468482905471432127537)
    ·
      refine ⟨16366851362179103574095653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21822468482905471432127537 16366851362179103574095653)
      ·
        refine ⟨3068784630408581920142935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16366851362179103574095653 3068784630408581920142935)
        ·
          refine ⟨4603176945612872880214403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3068784630408581920142935 4603176945612872880214403)
          ·
            refine ⟨6904765418419309320321605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4603176945612872880214403 6904765418419309320321605)
            ·
              refine ⟨1294643515953620497560301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6904765418419309320321605 1294643515953620497560301)
              ·
                refine ⟨485491318482607686585113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1294643515953620497560301 485491318482607686585113)
                ·
                  refine ⟨364118488861955764938835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 485491318482607686585113 364118488861955764938835)
                  ·
                    refine ⟨546177733292933647408253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 364118488861955764938835 546177733292933647408253)
                    ·
                      refine ⟨204816649984850117778095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 546177733292933647408253 204816649984850117778095)
                      ·
                        rfl

theorem cell23_398879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_398879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_398879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_398879 prefixEnd_398879 := by exact prefixLift 398879
  have htrace : WordTrace (prefixWord ++ tailWord_398879) baseStart_398879 baseEnd_398879 := by
    simpa [prefixWord, tailWord_398879, baseEnd_398879] using wordTrace_append hprefix tailTrace_398879
  have hstable : (prefixWord ++ tailWord_398879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398879).length < 2 ^ (prefixWord ++ tailWord_398879).sum := by decide
  have hdescent : baseEnd_398879 < baseStart_398879 := by decide
  rcases family_descends (prefixWord ++ tailWord_398879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398885 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 4, 3, 4]
def baseStart_398885 : Nat := 118140960795 + 398885 * 2 ^ 59
def prefixEnd_398885 : Nat := 4983230072969 + 3 ^ 40 * 398885 * 2
def baseEnd_398885 : Nat := 204819730868777094303067

theorem tailTrace_398885 : CollatzResearch.WordTrace tailWord_398885 prefixEnd_398885 204819730868777094303067 := by
  unfold tailWord_398885
  simp only [CollatzResearch.WordTrace]
  refine ⟨14548531159915243979470109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9699020773276829319646739 14548531159915243979470109)
  ·
    refine ⟨5455699184968216492301291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14548531159915243979470109 5455699184968216492301291)
    ·
      refine ⟨8183548777452324738451937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5455699184968216492301291 8183548777452324738451937)
      ·
        refine ⟨6137661583089243553838953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8183548777452324738451937 6137661583089243553838953)
        ·
          refine ⟨4603246187316932665379215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6137661583089243553838953 4603246187316932665379215)
          ·
            refine ⟨6904869280975398998068823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4603246187316932665379215 6904869280975398998068823)
            ·
              refine ⟨10357303921463098497103235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6904869280975398998068823 10357303921463098497103235)
              ·
                refine ⟨15535955882194647745654853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10357303921463098497103235 15535955882194647745654853)
                ·
                  refine ⟨2912991727911496452310285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15535955882194647745654853 2912991727911496452310285)
                  ·
                    refine ⟨1092371897966811169616357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2912991727911496452310285 1092371897966811169616357)
                    ·
                      refine ⟨204819730868777094303067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1092371897966811169616357 204819730868777094303067)
                      ·
                        rfl

theorem cell23_398885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_398885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_398885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_398885 prefixEnd_398885 := by exact prefixLift 398885
  have htrace : WordTrace (prefixWord ++ tailWord_398885) baseStart_398885 baseEnd_398885 := by
    simpa [prefixWord, tailWord_398885, baseEnd_398885] using wordTrace_append hprefix tailTrace_398885
  have hstable : (prefixWord ++ tailWord_398885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398885).length < 2 ^ (prefixWord ++ tailWord_398885).sum := by decide
  have hdescent : baseEnd_398885 < baseStart_398885 := by decide
  rcases family_descends (prefixWord ++ tailWord_398885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398932 : List Nat := [2, 4, 1, 1, 1, 2, 1, 3, 2, 2, 4]
def baseStart_398932 : Nat := 118140960795 + 398932 * 2 ^ 59
def prefixEnd_398932 : Nat := 4983230072969 + 3 ^ 40 * 398932 * 2
def baseEnd_398932 : Nat := 204843864459538410415351

theorem tailTrace_398932 : CollatzResearch.WordTrace tailWord_398932 prefixEnd_398932 204843864459538410415351 := by
  unfold tailWord_398932
  simp only [CollatzResearch.WordTrace]
  refine ⟨7275122695372485503215525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9700163593829980670954033 7275122695372485503215525)
  ·
    refine ⟨1364085505382341031852911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7275122695372485503215525 1364085505382341031852911)
    ·
      refine ⟨2046128258073511547779367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1364085505382341031852911 2046128258073511547779367)
      ·
        refine ⟨3069192387110267321669051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2046128258073511547779367 3069192387110267321669051)
        ·
          refine ⟨4603788580665400982503577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3069192387110267321669051 4603788580665400982503577)
          ·
            refine ⟨3452841435499050736877683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4603788580665400982503577 3452841435499050736877683)
            ·
              refine ⟨5179262153248576105316525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3452841435499050736877683 5179262153248576105316525)
              ·
                refine ⟨1942223307468216039493697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5179262153248576105316525 1942223307468216039493697)
                ·
                  refine ⟨1456667480601162029620273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1942223307468216039493697 1456667480601162029620273)
                  ·
                    refine ⟨1092500610450871522215205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1456667480601162029620273 1092500610450871522215205)
                    ·
                      refine ⟨204843864459538410415351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1092500610450871522215205 204843864459538410415351)
                      ·
                        rfl

theorem cell23_398932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_398932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_398932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_398932 prefixEnd_398932 := by exact prefixLift 398932
  have htrace : WordTrace (prefixWord ++ tailWord_398932) baseStart_398932 baseEnd_398932 := by
    simpa [prefixWord, tailWord_398932, baseEnd_398932] using wordTrace_append hprefix tailTrace_398932
  have hstable : (prefixWord ++ tailWord_398932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398932).length < 2 ^ (prefixWord ++ tailWord_398932).sum := by decide
  have hdescent : baseEnd_398932 < baseStart_398932 := by decide
  rcases family_descends (prefixWord ++ tailWord_398932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399006 : List Nat := [4, 3, 1, 1, 1, 3, 2, 1, 2, 5]
def baseStart_399006 : Nat := 118140960795 + 399006 * 2 ^ 59
def prefixEnd_399006 : Nat := 4983230072969 + 3 ^ 40 * 399006 * 2
def baseEnd_399006 : Nat := 68293954009323706963337

theorem tailTrace_399006 : CollatzResearch.WordTrace tailWord_399006 prefixEnd_399006 68293954009323706963337 := by
  unfold tailWord_399006
  simp only [CollatzResearch.WordTrace]
  refine ⟨1819118049059610205578109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9701962928317921096416581 1819118049059610205578109)
  ·
    refine ⟨682169268397353827091791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1819118049059610205578109 682169268397353827091791)
    ·
      refine ⟨1023253902596030740637687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 682169268397353827091791 1023253902596030740637687)
      ·
        refine ⟨1534880853894046110956531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1023253902596030740637687 1534880853894046110956531)
        ·
          refine ⟨2302321280841069166434797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1534880853894046110956531 2302321280841069166434797)
          ·
            refine ⟨863370480315400937413049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2302321280841069166434797 863370480315400937413049)
            ·
              refine ⟨647527860236550703059787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 863370480315400937413049 647527860236550703059787)
              ·
                refine ⟨971291790354826054589681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 647527860236550703059787 971291790354826054589681)
                ·
                  refine ⟨728468842766119540942261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 971291790354826054589681 728468842766119540942261)
                  ·
                    refine ⟨68293954009323706963337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 728468842766119540942261 68293954009323706963337)
                    ·
                      rfl

theorem cell23_399006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_399006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_399006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_399006 prefixEnd_399006 := by exact prefixLift 399006
  have htrace : WordTrace (prefixWord ++ tailWord_399006) baseStart_399006 baseEnd_399006 := by
    simpa [prefixWord, tailWord_399006, baseEnd_399006] using wordTrace_append hprefix tailTrace_399006
  have hstable : (prefixWord ++ tailWord_399006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399006).length < 2 ^ (prefixWord ++ tailWord_399006).sum := by decide
  have hdescent : baseEnd_399006 < baseStart_399006 := by decide
  rcases family_descends (prefixWord ++ tailWord_399006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399009 : List Nat := [1, 2, 3, 3, 2, 1, 1, 3, 2, 1, 4]
def baseStart_399009 : Nat := 118140960795 + 399009 * 2 ^ 59
def prefixEnd_399009 : Nat := 4983230072969 + 3 ^ 40 * 399009 * 2
def baseEnd_399009 : Nat := 204883402469934609152497

theorem tailTrace_399009 : CollatzResearch.WordTrace tailWord_399009 prefixEnd_399009 204883402469934609152497 := by
  unfold tailWord_399009
  simp only [CollatzResearch.WordTrace]
  refine ⟨14553053811466013156984081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9702035874310675437989387 14553053811466013156984081)
  ·
    refine ⟨10914790358599509867738061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14553053811466013156984081 10914790358599509867738061)
    ·
      refine ⟨4093046384474816200401773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10914790358599509867738061 4093046384474816200401773)
      ·
        refine ⟨1534892394178056075150665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4093046384474816200401773 1534892394178056075150665)
        ·
          refine ⟨1151169295633542056362999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1534892394178056075150665 1151169295633542056362999)
          ·
            refine ⟨1726753943450313084544499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1151169295633542056362999 1726753943450313084544499)
            ·
              refine ⟨2590130915175469626816749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1726753943450313084544499 2590130915175469626816749)
              ·
                refine ⟨971299093190801110056281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2590130915175469626816749 971299093190801110056281)
                ·
                  refine ⟨728474319893100832542211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 971299093190801110056281 728474319893100832542211)
                  ·
                    refine ⟨1092711479839651248813317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 728474319893100832542211 1092711479839651248813317)
                    ·
                      refine ⟨204883402469934609152497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1092711479839651248813317 204883402469934609152497)
                      ·
                        rfl

theorem cell23_399009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_399009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_399009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_399009 prefixEnd_399009 := by exact prefixLift 399009
  have htrace : WordTrace (prefixWord ++ tailWord_399009) baseStart_399009 baseEnd_399009 := by
    simpa [prefixWord, tailWord_399009, baseEnd_399009] using wordTrace_append hprefix tailTrace_399009
  have hstable : (prefixWord ++ tailWord_399009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399009).length < 2 ^ (prefixWord ++ tailWord_399009).sum := by decide
  have hdescent : baseEnd_399009 < baseStart_399009 := by decide
  rcases family_descends (prefixWord ++ tailWord_399009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399053 : List Nat := [1, 6, 2, 1, 1, 2, 1, 2, 3, 4]
def baseStart_399053 : Nat := 118140960795 + 399053 * 2 ^ 59
def prefixEnd_399053 : Nat := 4983230072969 + 3 ^ 40 * 399053 * 2
def baseEnd_399053 : Nat := 68301998539577479000765

theorem tailTrace_399053 : CollatzResearch.WordTrace tailWord_399053 prefixEnd_399053 68301998539577479000765 := by
  unfold tailWord_399053
  simp only [CollatzResearch.WordTrace]
  refine ⟨14554658623306608671585813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9703105748871072447723875 14554658623306608671585813)
  ·
    refine ⟨682249622967497281480585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14554658623306608671585813 682249622967497281480585)
    ·
      refine ⟨511687217225622961110439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 682249622967497281480585 511687217225622961110439)
      ·
        refine ⟨767530825838434441665659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 511687217225622961110439 767530825838434441665659)
        ·
          refine ⟨1151296238757651662498489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 767530825838434441665659 1151296238757651662498489)
          ·
            refine ⟨863472179068238746873867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1151296238757651662498489 863472179068238746873867)
            ·
              refine ⟨1295208268602358120310801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 863472179068238746873867 1295208268602358120310801)
              ·
                refine ⟨971406201451768590233101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1295208268602358120310801 971406201451768590233101)
                ·
                  refine ⟨364277325544413221337413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 971406201451768590233101 364277325544413221337413)
                  ·
                    refine ⟨68301998539577479000765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 364277325544413221337413 68301998539577479000765)
                    ·
                      rfl

theorem cell23_399053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_399053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_399053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_399053 prefixEnd_399053 := by exact prefixLift 399053
  have htrace : WordTrace (prefixWord ++ tailWord_399053) baseStart_399053 baseEnd_399053 := by
    simpa [prefixWord, tailWord_399053, baseEnd_399053] using wordTrace_append hprefix tailTrace_399053
  have hstable : (prefixWord ++ tailWord_399053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399053).length < 2 ^ (prefixWord ++ tailWord_399053).sum := by decide
  have hdescent : baseEnd_399053 < baseStart_399053 := by decide
  rcases family_descends (prefixWord ++ tailWord_399053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399086 : List Nat := [4, 1, 2, 1, 1, 2, 2, 1, 4, 3, 2]
def baseStart_399086 : Nat := 118140960795 + 399086 * 2 ^ 59
def prefixEnd_399086 : Nat := 4983230072969 + 3 ^ 40 * 399086 * 2
def baseEnd_399086 : Nat := 204922940480330807889643

theorem tailTrace_399086 : CollatzResearch.WordTrace tailWord_399086 prefixEnd_399086 204922940480330807889643 := by
  unfold tailWord_399086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1819482779023381913442139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9703908154791370205024741 1819482779023381913442139)
  ·
    refine ⟨2729224168535072870163209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1819482779023381913442139 2729224168535072870163209)
    ·
      refine ⟨2046918126401304652622407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2729224168535072870163209 2046918126401304652622407)
      ·
        refine ⟨3070377189601956978933611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2046918126401304652622407 3070377189601956978933611)
        ·
          refine ⟨4605565784402935468400417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3070377189601956978933611 4605565784402935468400417)
          ·
            refine ⟨3454174338302201601300313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4605565784402935468400417 3454174338302201601300313)
            ·
              refine ⟨2590630753726651200975235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3454174338302201601300313 2590630753726651200975235)
              ·
                refine ⟨3885946130589976801462853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2590630753726651200975235 3885946130589976801462853)
                ·
                  refine ⟨728614899485620650274285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3885946130589976801462853 728614899485620650274285)
                  ·
                    refine ⟨273230587307107743852857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 728614899485620650274285 273230587307107743852857)
                    ·
                      refine ⟨204922940480330807889643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 273230587307107743852857 204922940480330807889643)
                      ·
                        rfl

theorem cell23_399086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 4, 3, 2].length) (baseStart_399086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_399086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_399086 prefixEnd_399086 := by exact prefixLift 399086
  have htrace : WordTrace (prefixWord ++ tailWord_399086) baseStart_399086 baseEnd_399086 := by
    simpa [prefixWord, tailWord_399086, baseEnd_399086] using wordTrace_append hprefix tailTrace_399086
  have hstable : (prefixWord ++ tailWord_399086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399086).length < 2 ^ (prefixWord ++ tailWord_399086).sum := by decide
  have hdescent : baseEnd_399086 < baseStart_399086 := by decide
  rcases family_descends (prefixWord ++ tailWord_399086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399136 : List Nat := [2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 3]
def baseStart_399136 : Nat := 118140960795 + 399136 * 2 ^ 59
def prefixEnd_399136 : Nat := 4983230072969 + 3 ^ 40 * 399136 * 2
def baseEnd_399136 : Nat := 204948614513055612264413

theorem tailTrace_399136 : CollatzResearch.WordTrace tailWord_399136 prefixEnd_399136 204948614513055612264413 := by
  unfold tailWord_399136
  simp only [CollatzResearch.WordTrace]
  refine ⟨7278842941002956923428631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9705123921337275897904841 7278842941002956923428631)
  ·
    refine ⟨10918264411504435385142947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7278842941002956923428631 10918264411504435385142947)
    ·
      refine ⟨16377396617256653077714421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10918264411504435385142947 16377396617256653077714421)
      ·
        refine ⟨1535380932867811226035727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16377396617256653077714421 1535380932867811226035727)
        ·
          refine ⟨2303071399301716839053591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1535380932867811226035727 2303071399301716839053591)
          ·
            refine ⟨3454607098952575258580387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2303071399301716839053591 3454607098952575258580387)
            ·
              refine ⟨5181910648428862887870581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3454607098952575258580387 5181910648428862887870581)
              ·
                refine ⟨485804123290205895737867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5181910648428862887870581 485804123290205895737867)
                ·
                  refine ⟨728706184935308843606801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 485804123290205895737867 728706184935308843606801)
                  ·
                    refine ⟨546529638701481632705101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 728706184935308843606801 546529638701481632705101)
                    ·
                      refine ⟨204948614513055612264413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 546529638701481632705101 204948614513055612264413)
                      ·
                        rfl

theorem cell23_399136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_399136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_399136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_399136 prefixEnd_399136 := by exact prefixLift 399136
  have htrace : WordTrace (prefixWord ++ tailWord_399136) baseStart_399136 baseEnd_399136 := by
    simpa [prefixWord, tailWord_399136, baseEnd_399136] using wordTrace_append hprefix tailTrace_399136
  have hstable : (prefixWord ++ tailWord_399136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399136).length < 2 ^ (prefixWord ++ tailWord_399136).sum := by decide
  have hdescent : baseEnd_399136 < baseStart_399136 := by decide
  rcases family_descends (prefixWord ++ tailWord_399136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399156 : List Nat := [2, 5, 1, 1, 2, 2, 2, 8]
def baseStart_399156 : Nat := 118140960795 + 399156 * 2 ^ 59
def prefixEnd_399156 : Nat := 4983230072969 + 3 ^ 40 * 399156 * 2
def baseEnd_399156 : Nat := 7591069782449834593123

theorem tailTrace_399156 : CollatzResearch.WordTrace tailWord_399156 prefixEnd_399156 7591069782449834593123 := by
  unfold tailWord_399156
  simp only [CollatzResearch.WordTrace]
  refine ⟨7279207670966728631292661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9705610227955638175056881 7279207670966728631292661)
  ·
    refine ⟨682425719153130809183687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7279207670966728631292661 682425719153130809183687)
    ·
      refine ⟨1023638578729696213775531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 682425719153130809183687 1023638578729696213775531)
      ·
        refine ⟨1535457868094544320663297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1023638578729696213775531 1535457868094544320663297)
        ·
          refine ⟨1151593401070908240497473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1535457868094544320663297 1151593401070908240497473)
          ·
            refine ⟨863695050803181180373105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1151593401070908240497473 863695050803181180373105)
            ·
              refine ⟨647771288102385885279829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 863695050803181180373105 647771288102385885279829)
              ·
                refine ⟨7591069782449834593123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 647771288102385885279829 7591069782449834593123)
                ·
                  rfl

theorem cell23_399156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 8].length) (baseStart_399156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_399156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_399156 prefixEnd_399156 := by exact prefixLift 399156
  have htrace : WordTrace (prefixWord ++ tailWord_399156) baseStart_399156 baseEnd_399156 := by
    simpa [prefixWord, tailWord_399156, baseEnd_399156] using wordTrace_append hprefix tailTrace_399156
  have hstable : (prefixWord ++ tailWord_399156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399156).length < 2 ^ (prefixWord ++ tailWord_399156).sum := by decide
  have hdescent : baseEnd_399156 < baseStart_399156 := by decide
  rcases family_descends (prefixWord ++ tailWord_399156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399269 : List Nat := [1, 3, 1, 2, 1, 1, 1, 5, 1, 2, 5]
def baseStart_399269 : Nat := 118140960795 + 399269 * 2 ^ 59
def prefixEnd_399269 : Nat := 4983230072969 + 3 ^ 40 * 399269 * 2
def baseEnd_399269 : Nat := 205016907440103591901301

theorem tailTrace_399269 : CollatzResearch.WordTrace tailWord_399269 prefixEnd_399269 205016907440103591901301 := by
  unfold tailWord_399269
  simp only [CollatzResearch.WordTrace]
  refine ⟨14562536790524077561448861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9708357860349385040965907 14562536790524077561448861)
  ·
    refine ⟨5460951296446529085543323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14562536790524077561448861 5460951296446529085543323)
    ·
      refine ⟨8191426944669793628314985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5460951296446529085543323 8191426944669793628314985)
      ·
        refine ⟨6143570208502345221236239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8191426944669793628314985 6143570208502345221236239)
        ·
          refine ⟨9215355312753517831854359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6143570208502345221236239 9215355312753517831854359)
          ·
            refine ⟨13823032969130276747781539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9215355312753517831854359 13823032969130276747781539)
            ·
              refine ⟨20734549453695415121672309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13823032969130276747781539 20734549453695415121672309)
              ·
                refine ⟨1943864011283945167656779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20734549453695415121672309 1943864011283945167656779)
                ·
                  refine ⟨2915796016925917751485169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1943864011283945167656779 2915796016925917751485169)
                  ·
                    refine ⟨2186847012694438313613877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2915796016925917751485169 2186847012694438313613877)
                    ·
                      refine ⟨205016907440103591901301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2186847012694438313613877 205016907440103591901301)
                      ·
                        rfl

theorem cell23_399269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_399269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_399269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_399269 prefixEnd_399269 := by exact prefixLift 399269
  have htrace : WordTrace (prefixWord ++ tailWord_399269) baseStart_399269 baseEnd_399269 := by
    simpa [prefixWord, tailWord_399269, baseEnd_399269] using wordTrace_append hprefix tailTrace_399269
  have hstable : (prefixWord ++ tailWord_399269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399269).length < 2 ^ (prefixWord ++ tailWord_399269).sum := by decide
  have hdescent : baseEnd_399269 < baseStart_399269 := by decide
  rcases family_descends (prefixWord ++ tailWord_399269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399279 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 3, 3, 4]
def baseStart_399279 : Nat := 118140960795 + 399279 * 2 ^ 59
def prefixEnd_399279 : Nat := 4983230072969 + 3 ^ 40 * 399279 * 2
def baseEnd_399279 : Nat := 205022042246648552776255

theorem tailTrace_399279 : CollatzResearch.WordTrace tailWord_399279 prefixEnd_399279 205022042246648552776255 := by
  unfold tailWord_399279
  simp only [CollatzResearch.WordTrace]
  refine ⟨14562901520487849269312891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9708601013658566179541927 14562901520487849269312891)
  ·
    refine ⟨21844352280731773903969337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14562901520487849269312891 21844352280731773903969337)
    ·
      refine ⟨16383264210548830427977003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21844352280731773903969337 16383264210548830427977003)
      ·
        refine ⟨24574896315823245641965505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16383264210548830427977003 24574896315823245641965505)
        ·
          refine ⟨18431172236867434231474129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24574896315823245641965505 18431172236867434231474129)
          ·
            refine ⟨13823379177650575673605597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18431172236867434231474129 13823379177650575673605597)
            ·
              refine ⟨5183767191618965877602099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13823379177650575673605597 5183767191618965877602099)
              ·
                refine ⟨7775650787428448816403149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5183767191618965877602099 7775650787428448816403149)
                ·
                  refine ⟨2915869045285668306151181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7775650787428448816403149 2915869045285668306151181)
                  ·
                    refine ⟨1093450891982125614806693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2915869045285668306151181 1093450891982125614806693)
                    ·
                      refine ⟨205022042246648552776255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1093450891982125614806693 205022042246648552776255)
                      ·
                        rfl

theorem cell23_399279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3, 4].length) (baseStart_399279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_399279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_399279 prefixEnd_399279 := by exact prefixLift 399279
  have htrace : WordTrace (prefixWord ++ tailWord_399279) baseStart_399279 baseEnd_399279 := by
    simpa [prefixWord, tailWord_399279, baseEnd_399279] using wordTrace_append hprefix tailTrace_399279
  have hstable : (prefixWord ++ tailWord_399279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399279).length < 2 ^ (prefixWord ++ tailWord_399279).sum := by decide
  have hdescent : baseEnd_399279 < baseStart_399279 := by decide
  rcases family_descends (prefixWord ++ tailWord_399279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399289 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 2, 8]
def baseStart_399289 : Nat := 118140960795 + 399289 * 2 ^ 59
def prefixEnd_399289 : Nat := 4983230072969 + 3 ^ 40 * 399289 * 2
def baseEnd_399289 : Nat := 68342392351064504550403

theorem tailTrace_399289 : CollatzResearch.WordTrace tailWord_399289 prefixEnd_399289 68342392351064504550403 := by
  unfold tailWord_399289
  simp only [CollatzResearch.WordTrace]
  refine ⟨14563266250451620977176921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9708844166967747318117947 14563266250451620977176921)
  ·
    refine ⟨10922449687838715732882691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14563266250451620977176921 10922449687838715732882691)
    ·
      refine ⟨16383674531758073599324037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10922449687838715732882691 16383674531758073599324037)
      ·
        refine ⟨3071938974704638799873257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16383674531758073599324037 3071938974704638799873257)
        ·
          refine ⟨2303954231028479099904943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3071938974704638799873257 2303954231028479099904943)
          ·
            refine ⟨3455931346542718649857415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2303954231028479099904943 3455931346542718649857415)
            ·
              refine ⟨5183897019814077974786123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3455931346542718649857415 5183897019814077974786123)
              ·
                refine ⟨7775845529721116962179185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5183897019814077974786123 7775845529721116962179185)
                ·
                  refine ⟨5831884147290837721634389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7775845529721116962179185 5831884147290837721634389)
                  ·
                    refine ⟨68342392351064504550403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 5831884147290837721634389 68342392351064504550403)
                    ·
                      rfl

theorem cell23_399289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 8].length) (baseStart_399289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_399289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_399289 prefixEnd_399289 := by exact prefixLift 399289
  have htrace : WordTrace (prefixWord ++ tailWord_399289) baseStart_399289 baseEnd_399289 := by
    simpa [prefixWord, tailWord_399289, baseEnd_399289] using wordTrace_append hprefix tailTrace_399289
  have hstable : (prefixWord ++ tailWord_399289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399289).length < 2 ^ (prefixWord ++ tailWord_399289).sum := by decide
  have hdescent : baseEnd_399289 < baseStart_399289 := by decide
  rcases family_descends (prefixWord ++ tailWord_399289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399296 : List Nat := [2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 4]
def baseStart_399296 : Nat := 118140960795 + 399296 * 2 ^ 59
def prefixEnd_399296 : Nat := 4983230072969 + 3 ^ 40 * 399296 * 2
def baseEnd_399296 : Nat := 205030771417774986263677

theorem tailTrace_399296 : CollatzResearch.WordTrace tailWord_399296 prefixEnd_399296 205030771417774986263677 := by
  unfold tailWord_399296
  simp only [CollatzResearch.WordTrace]
  refine ⟨7281760780713130586340871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9709014374284174115121161 7281760780713130586340871)
  ·
    refine ⟨10922641171069695879511307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7281760780713130586340871 10922641171069695879511307)
    ·
      refine ⟨16383961756604543819266961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10922641171069695879511307 16383961756604543819266961)
      ·
        refine ⟨12287971317453407864450221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16383961756604543819266961 12287971317453407864450221)
        ·
          refine ⟨4607989244045027949168833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12287971317453407864450221 4607989244045027949168833)
          ·
            refine ⟨3455991933033770961876625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4607989244045027949168833 3455991933033770961876625)
            ·
              refine ⟨2591993949775328221407469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3455991933033770961876625 2591993949775328221407469)
              ·
                refine ⟨971997731165748083027801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2591993949775328221407469 971997731165748083027801)
                ·
                  refine ⟨728998298374311062270851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 971997731165748083027801 728998298374311062270851)
                  ·
                    refine ⟨1093497447561466593406277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 728998298374311062270851 1093497447561466593406277)
                    ·
                      refine ⟨205030771417774986263677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1093497447561466593406277 205030771417774986263677)
                      ·
                        rfl

theorem cell23_399296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 4].length) (baseStart_399296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_399296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_399296 prefixEnd_399296 := by exact prefixLift 399296
  have htrace : WordTrace (prefixWord ++ tailWord_399296) baseStart_399296 baseEnd_399296 := by
    simpa [prefixWord, tailWord_399296, baseEnd_399296] using wordTrace_append hprefix tailTrace_399296
  have hstable : (prefixWord ++ tailWord_399296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399296).length < 2 ^ (prefixWord ++ tailWord_399296).sum := by decide
  have hdescent : baseEnd_399296 < baseStart_399296 := by decide
  rcases family_descends (prefixWord ++ tailWord_399296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399306 : List Nat := [3, 1, 2, 1, 2, 1, 2, 2, 5, 4]
def baseStart_399306 : Nat := 118140960795 + 399306 * 2 ^ 59
def prefixEnd_399306 : Nat := 4983230072969 + 3 ^ 40 * 399306 * 2
def baseEnd_399306 : Nat := 68345302074773315712877

theorem tailTrace_399306 : CollatzResearch.WordTrace tailWord_399306 prefixEnd_399306 68345302074773315712877 := by
  unfold tailWord_399306
  simp only [CollatzResearch.WordTrace]
  refine ⟨3640971572847508220136443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9709257527593355253697181 3640971572847508220136443)
  ·
    refine ⟨5461457359271262330204665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3640971572847508220136443 5461457359271262330204665)
    ·
      refine ⟨4096093019453446747653499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5461457359271262330204665 4096093019453446747653499)
      ·
        refine ⟨6144139529180170121480249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4096093019453446747653499 6144139529180170121480249)
        ·
          refine ⟨4608104646885127591110187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6144139529180170121480249 4608104646885127591110187)
          ·
            refine ⟨6912156970327691386665281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4608104646885127591110187 6912156970327691386665281)
            ·
              refine ⟨5184117727745768539998961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6912156970327691386665281 5184117727745768539998961)
              ·
                refine ⟨3888088295809326404999221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5184117727745768539998961 3888088295809326404999221)
                ·
                  refine ⟨364508277732124350468677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3888088295809326404999221 364508277732124350468677)
                  ·
                    refine ⟨68345302074773315712877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 364508277732124350468677 68345302074773315712877)
                    ·
                      rfl

theorem cell23_399306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 5, 4].length) (baseStart_399306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_399306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_399306 prefixEnd_399306 := by exact prefixLift 399306
  have htrace : WordTrace (prefixWord ++ tailWord_399306) baseStart_399306 baseEnd_399306 := by
    simpa [prefixWord, tailWord_399306, baseEnd_399306] using wordTrace_append hprefix tailTrace_399306
  have hstable : (prefixWord ++ tailWord_399306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399306).length < 2 ^ (prefixWord ++ tailWord_399306).sum := by decide
  have hdescent : baseEnd_399306 < baseStart_399306 := by decide
  rcases family_descends (prefixWord ++ tailWord_399306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399319 : List Nat := [1, 1, 3, 2, 1, 1, 3, 3, 8]
def baseStart_399319 : Nat := 118140960795 + 399319 * 2 ^ 59
def prefixEnd_399319 : Nat := 4983230072969 + 3 ^ 40 * 399319 * 2
def baseEnd_399319 : Nat := 22782509052536488475119

theorem tailTrace_399319 : CollatzResearch.WordTrace tailWord_399319 prefixEnd_399319 22782509052536488475119 := by
  unfold tailWord_399319
  simp only [CollatzResearch.WordTrace]
  refine ⟨14564360440342936100769011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9709573626895290733846007 14564360440342936100769011)
  ·
    refine ⟨21846540660514404151153517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14564360440342936100769011 21846540660514404151153517)
    ·
      refine ⟨8192452747692901556682569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21846540660514404151153517 8192452747692901556682569)
      ·
        refine ⟨6144339560769676167511927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8192452747692901556682569 6144339560769676167511927)
        ·
          refine ⟨9216509341154514251267891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6144339560769676167511927 9216509341154514251267891)
          ·
            refine ⟨13824764011731771376901837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9216509341154514251267891 13824764011731771376901837)
            ·
              refine ⟨5184286504399414266338189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13824764011731771376901837 5184286504399414266338189)
              ·
                refine ⟨1944107439149780349876821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5184286504399414266338189 1944107439149780349876821)
                ·
                  refine ⟨22782509052536488475119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1944107439149780349876821 22782509052536488475119)
                  ·
                    rfl

theorem cell23_399319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 8].length) (baseStart_399319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_399319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_399319 prefixEnd_399319 := by exact prefixLift 399319
  have htrace : WordTrace (prefixWord ++ tailWord_399319) baseStart_399319 baseEnd_399319 := by
    simpa [prefixWord, tailWord_399319, baseEnd_399319] using wordTrace_append hprefix tailTrace_399319
  have hstable : (prefixWord ++ tailWord_399319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399319).length < 2 ^ (prefixWord ++ tailWord_399319).sum := by decide
  have hdescent : baseEnd_399319 < baseStart_399319 := by decide
  rcases family_descends (prefixWord ++ tailWord_399319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399339 : List Nat := [1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 6]
def baseStart_399339 : Nat := 118140960795 + 399339 * 2 ^ 59
def prefixEnd_399339 : Nat := 4983230072969 + 3 ^ 40 * 399339 * 2
def baseEnd_399339 : Nat := 205052851085918318025979

theorem tailTrace_399339 : CollatzResearch.WordTrace tailWord_399339 prefixEnd_399339 205052851085918318025979 := by
  unfold tailWord_399339
  simp only [CollatzResearch.WordTrace]
  refine ⟨14565089900270479516497071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9710059933513653010998047 14565089900270479516497071)
  ·
    refine ⟨21847634850405719274745607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14565089900270479516497071 21847634850405719274745607)
    ·
      refine ⟨32771452275608578912118411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21847634850405719274745607 32771452275608578912118411)
      ·
        refine ⟨49157178413412868368177617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32771452275608578912118411 49157178413412868368177617)
        ·
          refine ⟨36867883810059651276133213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49157178413412868368177617 36867883810059651276133213)
          ·
            refine ⟨13825456428772369228549955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36867883810059651276133213 13825456428772369228549955)
            ·
              refine ⟨20738184643158553842824933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13825456428772369228549955 20738184643158553842824933)
              ·
                refine ⟨3888409620592228845529675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20738184643158553842824933 3888409620592228845529675)
                ·
                  refine ⟨5832614430888343268294513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3888409620592228845529675 5832614430888343268294513)
                  ·
                    refine ⟨4374460823166257451220885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5832614430888343268294513 4374460823166257451220885)
                    ·
                      refine ⟨205052851085918318025979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4374460823166257451220885 205052851085918318025979)
                      ·
                        rfl

theorem cell23_399339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 6].length) (baseStart_399339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_399339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_399339 prefixEnd_399339 := by exact prefixLift 399339
  have htrace : WordTrace (prefixWord ++ tailWord_399339) baseStart_399339 baseEnd_399339 := by
    simpa [prefixWord, tailWord_399339, baseEnd_399339] using wordTrace_append hprefix tailTrace_399339
  have hstable : (prefixWord ++ tailWord_399339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399339).length < 2 ^ (prefixWord ++ tailWord_399339).sum := by decide
  have hdescent : baseEnd_399339 < baseStart_399339 := by decide
  rcases family_descends (prefixWord ++ tailWord_399339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399359 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 7]
def baseStart_399359 : Nat := 118140960795 + 399359 * 2 ^ 59
def prefixEnd_399359 : Nat := 4983230072969 + 3 ^ 40 * 399359 * 2
def baseEnd_399359 : Nat := 205063120699008239775887

theorem tailTrace_399359 : CollatzResearch.WordTrace tailWord_399359 prefixEnd_399359 205063120699008239775887 := by
  unfold tailWord_399359
  simp only [CollatzResearch.WordTrace]
  refine ⟨14565819360198022932225131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9710546240132015288150087 14565819360198022932225131)
  ·
    refine ⟨21848729040297034398337697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14565819360198022932225131 21848729040297034398337697)
    ·
      refine ⟨16386546780222775798753273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21848729040297034398337697 16386546780222775798753273)
      ·
        refine ⟨12289910085167081849064955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16386546780222775798753273 12289910085167081849064955)
        ·
          refine ⟨18434865127750622773597433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12289910085167081849064955 18434865127750622773597433)
          ·
            refine ⟨13826148845812967080198075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18434865127750622773597433 13826148845812967080198075)
            ·
              refine ⟨20739223268719450620297113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13826148845812967080198075 20739223268719450620297113)
              ·
                refine ⟨15554417451539587965222835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20739223268719450620297113 15554417451539587965222835)
                ·
                  refine ⟨23331626177309381947834253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15554417451539587965222835 23331626177309381947834253)
                  ·
                    refine ⟨8749359816491018230437845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23331626177309381947834253 8749359816491018230437845)
                    ·
                      refine ⟨205063120699008239775887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 8749359816491018230437845 205063120699008239775887)
                      ·
                        rfl

theorem cell23_399359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_399359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_399359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_399359 prefixEnd_399359 := by exact prefixLift 399359
  have htrace : WordTrace (prefixWord ++ tailWord_399359) baseStart_399359 baseEnd_399359 := by
    simpa [prefixWord, tailWord_399359, baseEnd_399359] using wordTrace_append hprefix tailTrace_399359
  have hstable : (prefixWord ++ tailWord_399359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399359).length < 2 ^ (prefixWord ++ tailWord_399359).sum := by decide
  have hdescent : baseEnd_399359 < baseStart_399359 := by decide
  rcases family_descends (prefixWord ++ tailWord_399359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399414 : List Nat := [5, 1, 2, 1, 1, 1, 4, 3, 1, 1, 3]
def baseStart_399414 : Nat := 118140960795 + 399414 * 2 ^ 59
def prefixEnd_399414 : Nat := 4983230072969 + 3 ^ 40 * 399414 * 2
def baseEnd_399414 : Nat := 205091362135005524588135

theorem tailTrace_399414 : CollatzResearch.WordTrace tailWord_399414 prefixEnd_399414 205091362135005524588135 := by
  unfold tailWord_399414
  simp only [CollatzResearch.WordTrace]
  refine ⟨910489085937422957842331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9711883583332511550318197 910489085937422957842331)
  ·
    refine ⟨1365733628906134436763497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 910489085937422957842331 1365733628906134436763497)
    ·
      refine ⟨1024300221679600827572623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1365733628906134436763497 1024300221679600827572623)
      ·
        refine ⟨1536450332519401241358935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1024300221679600827572623 1536450332519401241358935)
        ·
          refine ⟨2304675498779101862038403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1536450332519401241358935 2304675498779101862038403)
          ·
            refine ⟨3457013248168652793057605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2304675498779101862038403 3457013248168652793057605)
            ·
              refine ⟨648189984031622398698301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3457013248168652793057605 648189984031622398698301)
              ·
                refine ⟨243071244011858399511863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 648189984031622398698301 243071244011858399511863)
                ·
                  refine ⟨364606866017787599267795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 243071244011858399511863 364606866017787599267795)
                  ·
                    refine ⟨546910299026681398901693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 364606866017787599267795 546910299026681398901693)
                    ·
                      refine ⟨205091362135005524588135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 546910299026681398901693 205091362135005524588135)
                      ·
                        rfl

theorem cell23_399414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_399414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_399414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_399414 prefixEnd_399414 := by exact prefixLift 399414
  have htrace : WordTrace (prefixWord ++ tailWord_399414) baseStart_399414 baseEnd_399414 := by
    simpa [prefixWord, tailWord_399414, baseEnd_399414] using wordTrace_append hprefix tailTrace_399414
  have hstable : (prefixWord ++ tailWord_399414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399414).length < 2 ^ (prefixWord ++ tailWord_399414).sum := by decide
  have hdescent : baseEnd_399414 < baseStart_399414 := by decide
  rcases family_descends (prefixWord ++ tailWord_399414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399417 : List Nat := [1, 2, 1, 5, 3, 2, 2, 1, 1, 5]
def baseStart_399417 : Nat := 118140960795 + 399417 * 2 ^ 59
def prefixEnd_399417 : Nat := 4983230072969 + 3 ^ 40 * 399417 * 2
def baseEnd_399417 : Nat := 68364300858989670950207

theorem tailTrace_399417 : CollatzResearch.WordTrace tailWord_399417 prefixEnd_399417 68364300858989670950207 := by
  unfold tailWord_399417
  simp only [CollatzResearch.WordTrace]
  refine ⟨14567934793987898837836505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9711956529325265891891003 14567934793987898837836505)
  ·
    refine ⟨10925951095490924128377379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14567934793987898837836505 10925951095490924128377379)
    ·
      refine ⟨16388926643236386192566069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10925951095490924128377379 16388926643236386192566069)
      ·
        refine ⟨1536461872803411205553069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16388926643236386192566069 1536461872803411205553069)
        ·
          refine ⟨576173202301279202082401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1536461872803411205553069 576173202301279202082401)
          ·
            refine ⟨432129901725959401561801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 576173202301279202082401 432129901725959401561801)
            ·
              refine ⟨324097426294469551171351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 432129901725959401561801 324097426294469551171351)
              ·
                refine ⟨486146139441704326757027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 324097426294469551171351 486146139441704326757027)
                ·
                  refine ⟨729219209162556490135541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 486146139441704326757027 729219209162556490135541)
                  ·
                    refine ⟨68364300858989670950207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 729219209162556490135541 68364300858989670950207)
                    ·
                      rfl

theorem cell23_399417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 1, 1, 5].length) (baseStart_399417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_399417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_399417 prefixEnd_399417 := by exact prefixLift 399417
  have htrace : WordTrace (prefixWord ++ tailWord_399417) baseStart_399417 baseEnd_399417 := by
    simpa [prefixWord, tailWord_399417, baseEnd_399417] using wordTrace_append hprefix tailTrace_399417
  have hstable : (prefixWord ++ tailWord_399417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399417).length < 2 ^ (prefixWord ++ tailWord_399417).sum := by decide
  have hdescent : baseEnd_399417 < baseStart_399417 := by decide
  rcases family_descends (prefixWord ++ tailWord_399417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399420 : List Nat := [2, 2, 2, 2, 2, 1, 1, 2, 5, 2, 2]
def baseStart_399420 : Nat := 118140960795 + 399420 * 2 ^ 59
def prefixEnd_399420 : Nat := 4983230072969 + 3 ^ 40 * 399420 * 2
def baseEnd_399420 : Nat := 205094443018932501113107

theorem tailTrace_399420 : CollatzResearch.WordTrace tailWord_399420 prefixEnd_399420 205094443018932501113107 := by
  unfold tailWord_399420
  simp only [CollatzResearch.WordTrace]
  refine ⟨7284022106488515175097857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9712029475318020233463809 7284022106488515175097857)
  ·
    refine ⟨5463016579866386381323393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7284022106488515175097857 5463016579866386381323393)
    ·
      refine ⟨4097262434899789785992545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5463016579866386381323393 4097262434899789785992545)
      ·
        refine ⟨3072946826174842339494409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4097262434899789785992545 3072946826174842339494409)
        ·
          refine ⟨2304710119631131754620807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3072946826174842339494409 2304710119631131754620807)
          ·
            refine ⟨3457065179446697631931211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2304710119631131754620807 3457065179446697631931211)
            ·
              refine ⟨5185597769170046447896817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3457065179446697631931211 5185597769170046447896817)
              ·
                refine ⟨3889198326877534835922613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5185597769170046447896817 3889198326877534835922613)
                ·
                  refine ⟨364612343144768890867745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3889198326877534835922613 364612343144768890867745)
                  ·
                    refine ⟨273459257358576668150809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 364612343144768890867745 273459257358576668150809)
                    ·
                      refine ⟨205094443018932501113107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 273459257358576668150809 205094443018932501113107)
                      ·
                        rfl

theorem cell23_399420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 5, 2, 2].length) (baseStart_399420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_399420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_399420 prefixEnd_399420 := by exact prefixLift 399420
  have htrace : WordTrace (prefixWord ++ tailWord_399420) baseStart_399420 baseEnd_399420 := by
    simpa [prefixWord, tailWord_399420, baseEnd_399420] using wordTrace_append hprefix tailTrace_399420
  have hstable : (prefixWord ++ tailWord_399420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399420).length < 2 ^ (prefixWord ++ tailWord_399420).sum := by decide
  have hdescent : baseEnd_399420 < baseStart_399420 := by decide
  rcases family_descends (prefixWord ++ tailWord_399420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399470 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3]
def baseStart_399470 : Nat := 118140960795 + 399470 * 2 ^ 59
def prefixEnd_399470 : Nat := 4983230072969 + 3 ^ 40 * 399470 * 2
def baseEnd_399470 : Nat := 205120117051657305487877

theorem tailTrace_399470 : CollatzResearch.WordTrace tailWord_399470 prefixEnd_399470 205120117051657305487877 := by
  unfold tailWord_399470
  simp only [CollatzResearch.WordTrace]
  refine ⟨1821233482849486111189483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9713245241863925926343909 1821233482849486111189483)
  ·
    refine ⟨2731850224274229166784225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1821233482849486111189483 2731850224274229166784225)
    ·
      refine ⟨2048887668205671875088169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2731850224274229166784225 2048887668205671875088169)
      ·
        refine ⟨1536665751154253906316127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2048887668205671875088169 1536665751154253906316127)
        ·
          refine ⟨2304998626731380859474191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1536665751154253906316127 2304998626731380859474191)
          ·
            refine ⟨3457497940097071289211287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2304998626731380859474191 3457497940097071289211287)
            ·
              refine ⟨5186246910145606933816931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3457497940097071289211287 5186246910145606933816931)
              ·
                refine ⟨7779370365218410400725397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5186246910145606933816931 7779370365218410400725397)
                ·
                  refine ⟨364657985869612987534003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7779370365218410400725397 364657985869612987534003)
                  ·
                    refine ⟨546986978804419481301005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 364657985869612987534003 546986978804419481301005)
                    ·
                      refine ⟨205120117051657305487877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 546986978804419481301005 205120117051657305487877)
                      ·
                        rfl

theorem cell23_399470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_399470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_399470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_399470 prefixEnd_399470 := by exact prefixLift 399470
  have htrace : WordTrace (prefixWord ++ tailWord_399470) baseStart_399470 baseEnd_399470 := by
    simpa [prefixWord, tailWord_399470, baseEnd_399470] using wordTrace_append hprefix tailTrace_399470
  have hstable : (prefixWord ++ tailWord_399470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399470).length < 2 ^ (prefixWord ++ tailWord_399470).sum := by decide
  have hdescent : baseEnd_399470 < baseStart_399470 := by decide
  rcases family_descends (prefixWord ++ tailWord_399470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399536 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 6]
def baseStart_399536 : Nat := 118140960795 + 399536 * 2 ^ 59
def prefixEnd_399536 : Nat := 4983230072969 + 3 ^ 40 * 399536 * 2
def baseEnd_399536 : Nat := 205154006774854047262573

theorem tailTrace_399536 : CollatzResearch.WordTrace tailWord_399536 prefixEnd_399536 205154006774854047262573 := by
  unfold tailWord_399536
  simp only [CollatzResearch.WordTrace]
  refine ⟨7286137540278391080709231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9714850053704521440945641 7286137540278391080709231)
  ·
    refine ⟨10929206310417586621063847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7286137540278391080709231 10929206310417586621063847)
    ·
      refine ⟨16393809465626379931595771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10929206310417586621063847 16393809465626379931595771)
      ·
        refine ⟨24590714198439569897393657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16393809465626379931595771 24590714198439569897393657)
        ·
          refine ⟨18443035648829677423045243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24590714198439569897393657 18443035648829677423045243)
          ·
            refine ⟨27664553473244516134567865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18443035648829677423045243 27664553473244516134567865)
            ·
              refine ⟨20748415104933387100925899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27664553473244516134567865 20748415104933387100925899)
              ·
                refine ⟨31122622657400080651388849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20748415104933387100925899 31122622657400080651388849)
                ·
                  refine ⟨23341966993050060488541637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31122622657400080651388849 23341966993050060488541637)
                  ·
                    refine ⟨4376618811196886341601557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23341966993050060488541637 4376618811196886341601557)
                    ·
                      refine ⟨205154006774854047262573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4376618811196886341601557 205154006774854047262573)
                      ·
                        rfl

theorem cell23_399536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 6].length) (baseStart_399536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_399536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_399536 prefixEnd_399536 := by exact prefixLift 399536
  have htrace : WordTrace (prefixWord ++ tailWord_399536) baseStart_399536 baseEnd_399536 := by
    simpa [prefixWord, tailWord_399536, baseEnd_399536] using wordTrace_append hprefix tailTrace_399536
  have hstable : (prefixWord ++ tailWord_399536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399536).length < 2 ^ (prefixWord ++ tailWord_399536).sum := by decide
  have hdescent : baseEnd_399536 < baseStart_399536 := by decide
  rcases family_descends (prefixWord ++ tailWord_399536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399610 : List Nat := [3, 1, 1, 1, 1, 5, 1, 3, 3, 4]
def baseStart_399610 : Nat := 118140960795 + 399610 * 2 ^ 59
def prefixEnd_399610 : Nat := 4983230072969 + 3 ^ 40 * 399610 * 2
def baseEnd_399610 : Nat := 68397334781095585912411

theorem tailTrace_399610 : CollatzResearch.WordTrace tailWord_399610 prefixEnd_399610 68397334781095585912411 := by
  unfold tailWord_399610
  simp only [CollatzResearch.WordTrace]
  refine ⟨3643743520572173199903071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9716649388192461866408189 3643743520572173199903071)
  ·
    refine ⟨5465615280858259799854607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3643743520572173199903071 5465615280858259799854607)
    ·
      refine ⟨8198422921287389699781911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5465615280858259799854607 8198422921287389699781911)
      ·
        refine ⟨12297634381931084549672867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8198422921287389699781911 12297634381931084549672867)
        ·
          refine ⟨18446451572896626824509301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12297634381931084549672867 18446451572896626824509301)
          ·
            refine ⟨1729354834959058764797747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18446451572896626824509301 1729354834959058764797747)
            ·
              refine ⟨2594032252438588147196621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1729354834959058764797747 2594032252438588147196621)
              ·
                refine ⟨972762094664470555198733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2594032252438588147196621 972762094664470555198733)
                ·
                  refine ⟨364785785499176458199525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 972762094664470555198733 364785785499176458199525)
                  ·
                    refine ⟨68397334781095585912411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 364785785499176458199525 68397334781095585912411)
                    ·
                      rfl

theorem cell23_399610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 3, 4].length) (baseStart_399610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_399610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_399610 prefixEnd_399610 := by exact prefixLift 399610
  have htrace : WordTrace (prefixWord ++ tailWord_399610) baseStart_399610 baseEnd_399610 := by
    simpa [prefixWord, tailWord_399610, baseEnd_399610] using wordTrace_append hprefix tailTrace_399610
  have hstable : (prefixWord ++ tailWord_399610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399610).length < 2 ^ (prefixWord ++ tailWord_399610).sum := by decide
  have hdescent : baseEnd_399610 < baseStart_399610 := by decide
  rcases family_descends (prefixWord ++ tailWord_399610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399661 : List Nat := [1, 5, 3, 1, 2, 2, 1, 1, 3, 4]
def baseStart_399661 : Nat := 118140960795 + 399661 * 2 ^ 59
def prefixEnd_399661 : Nat := 4983230072969 + 3 ^ 40 * 399661 * 2
def baseEnd_399661 : Nat := 68406063952222019399833

theorem tailTrace_399661 : CollatzResearch.WordTrace tailWord_399661 prefixEnd_399661 68406063952222019399833 := by
  unfold tailWord_399661
  simp only [CollatzResearch.WordTrace]
  refine ⟨14576834205103928509718837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9717889470069285673145891 14576834205103928509718837)
  ·
    refine ⟨1366578206728493297786141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14576834205103928509718837 1366578206728493297786141)
    ·
      refine ⟨512466827523184986669803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1366578206728493297786141 512466827523184986669803)
      ·
        refine ⟨768700241284777480004705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 512466827523184986669803 768700241284777480004705)
        ·
          refine ⟨576525180963583110003529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 768700241284777480004705 576525180963583110003529)
          ·
            refine ⟨432393885722687332502647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 576525180963583110003529 432393885722687332502647)
            ·
              refine ⟨648590828584030998753971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432393885722687332502647 648590828584030998753971)
              ·
                refine ⟨972886242876046498130957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 648590828584030998753971 972886242876046498130957)
                ·
                  refine ⟨364832341078517436799109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 972886242876046498130957 364832341078517436799109)
                  ·
                    refine ⟨68406063952222019399833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 364832341078517436799109 68406063952222019399833)
                    ·
                      rfl

theorem cell23_399661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_399661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_399661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_399661 prefixEnd_399661 := by exact prefixLift 399661
  have htrace : WordTrace (prefixWord ++ tailWord_399661) baseStart_399661 baseEnd_399661 := by
    simpa [prefixWord, tailWord_399661, baseEnd_399661] using wordTrace_append hprefix tailTrace_399661
  have hstable : (prefixWord ++ tailWord_399661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399661).length < 2 ^ (prefixWord ++ tailWord_399661).sum := by decide
  have hdescent : baseEnd_399661 < baseStart_399661 := by decide
  rcases family_descends (prefixWord ++ tailWord_399661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399700 : List Nat := [2, 4, 1, 1, 2, 2, 1, 1, 3, 6]
def baseStart_399700 : Nat := 118140960795 + 399700 * 2 ^ 59
def prefixEnd_399700 : Nat := 4983230072969 + 3 ^ 40 * 399700 * 2
def baseEnd_399700 : Nat := 68412739200730468537273

theorem tailTrace_399700 : CollatzResearch.WordTrace tailWord_399700 prefixEnd_399700 68412739200730468537273 := by
  unfold tailWord_399700
  simp only [CollatzResearch.WordTrace]
  refine ⟨7289128325981319085194277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9718837767975092113592369 7289128325981319085194277)
  ·
    refine ⟨1366711561121497328473927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7289128325981319085194277 1366711561121497328473927)
    ·
      refine ⟨2050067341682245992710891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1366711561121497328473927 2050067341682245992710891)
      ·
        refine ⟨3075101012523368989066337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2050067341682245992710891 3075101012523368989066337)
        ·
          refine ⟨2306325759392526741799753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3075101012523368989066337 2306325759392526741799753)
          ·
            refine ⟨1729744319544395056349815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2306325759392526741799753 1729744319544395056349815)
            ·
              refine ⟨2594616479316592584524723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1729744319544395056349815 2594616479316592584524723)
              ·
                refine ⟨3891924718974888876787085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2594616479316592584524723 3891924718974888876787085)
                ·
                  refine ⟨1459471769615583328795157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3891924718974888876787085 1459471769615583328795157)
                  ·
                    refine ⟨68412739200730468537273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1459471769615583328795157 68412739200730468537273)
                    ·
                      rfl

theorem cell23_399700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_399700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_399700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_399700 prefixEnd_399700 := by exact prefixLift 399700
  have htrace : WordTrace (prefixWord ++ tailWord_399700) baseStart_399700 baseEnd_399700 := by
    simpa [prefixWord, tailWord_399700, baseEnd_399700] using wordTrace_append hprefix tailTrace_399700
  have hstable : (prefixWord ++ tailWord_399700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399700).length < 2 ^ (prefixWord ++ tailWord_399700).sum := by decide
  have hdescent : baseEnd_399700 < baseStart_399700 := by decide
  rcases family_descends (prefixWord ++ tailWord_399700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399717 : List Nat := [1, 3, 1, 3, 1, 3, 1, 4, 2, 4]
def baseStart_399717 : Nat := 118140960795 + 399717 * 2 ^ 59
def prefixEnd_399717 : Nat := 4983230072969 + 3 ^ 40 * 399717 * 2
def baseEnd_399717 : Nat := 68415648924439279699747

theorem tailTrace_399717 : CollatzResearch.WordTrace tailWord_399717 prefixEnd_399717 68415648924439279699747 := by
  unfold tailWord_399717
  simp only [CollatzResearch.WordTrace]
  refine ⟨14578876692901050073757405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9719251128600700049171603 14578876692901050073757405)
  ·
    refine ⟨5467078759837893777659027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14578876692901050073757405 5467078759837893777659027)
    ·
      refine ⟨8200618139756840666488541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5467078759837893777659027 8200618139756840666488541)
      ·
        refine ⟨3075231802408815249933203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8200618139756840666488541 3075231802408815249933203)
        ·
          refine ⟨4612847703613222874899805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3075231802408815249933203 4612847703613222874899805)
          ·
            refine ⟨1729817888854958578087427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4612847703613222874899805 1729817888854958578087427)
            ·
              refine ⟨2594726833282437867131141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1729817888854958578087427 2594726833282437867131141)
              ·
                refine ⟨486511281240457100087089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2594726833282437867131141 486511281240457100087089)
                ·
                  refine ⟨364883460930342825065317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 486511281240457100087089 364883460930342825065317)
                  ·
                    refine ⟨68415648924439279699747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 364883460930342825065317 68415648924439279699747)
                    ·
                      rfl

theorem cell23_399717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4, 2, 4].length) (baseStart_399717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_399717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_399717 prefixEnd_399717 := by exact prefixLift 399717
  have htrace : WordTrace (prefixWord ++ tailWord_399717) baseStart_399717 baseEnd_399717 := by
    simpa [prefixWord, tailWord_399717, baseEnd_399717] using wordTrace_append hprefix tailTrace_399717
  have hstable : (prefixWord ++ tailWord_399717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399717).length < 2 ^ (prefixWord ++ tailWord_399717).sum := by decide
  have hdescent : baseEnd_399717 < baseStart_399717 := by decide
  rcases family_descends (prefixWord ++ tailWord_399717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399730 : List Nat := [3, 2, 1, 2, 1, 3, 3, 8]
def baseStart_399730 : Nat := 118140960795 + 399730 * 2 ^ 59
def prefixEnd_399730 : Nat := 4983230072969 + 3 ^ 40 * 399730 * 2
def baseEnd_399730 : Nat := 7601986000808381045803

theorem tailTrace_399730 : CollatzResearch.WordTrace tailWord_399730 prefixEnd_399730 7601986000808381045803 := by
  unfold tailWord_399730
  simp only [CollatzResearch.WordTrace]
  refine ⟨3644837710463488323495161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9719567227902635529320429 3644837710463488323495161)
  ·
    refine ⟨2733628282847616242621371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3644837710463488323495161 2733628282847616242621371)
    ·
      refine ⟨4100442424271424363932057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2733628282847616242621371 4100442424271424363932057)
      ·
        refine ⟨3075331818203568272949043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4100442424271424363932057 3075331818203568272949043)
        ·
          refine ⟨4612997727305352409423565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3075331818203568272949043 4612997727305352409423565)
          ·
            refine ⟨1729874147739507153533837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4612997727305352409423565 1729874147739507153533837)
            ·
              refine ⟨648702805402315182575189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1729874147739507153533837 648702805402315182575189)
              ·
                refine ⟨7601986000808381045803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 648702805402315182575189 7601986000808381045803)
                ·
                  rfl

theorem cell23_399730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 8].length) (baseStart_399730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_399730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_399730 prefixEnd_399730 := by exact prefixLift 399730
  have htrace : WordTrace (prefixWord ++ tailWord_399730) baseStart_399730 baseEnd_399730 := by
    simpa [prefixWord, tailWord_399730, baseEnd_399730] using wordTrace_append hprefix tailTrace_399730
  have hstable : (prefixWord ++ tailWord_399730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399730).length < 2 ^ (prefixWord ++ tailWord_399730).sum := by decide
  have hdescent : baseEnd_399730 < baseStart_399730 := by decide
  rcases family_descends (prefixWord ++ tailWord_399730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399747 : List Nat := [1, 1, 1, 3, 6, 1, 3, 7]
def baseStart_399747 : Nat := 118140960795 + 399747 * 2 ^ 59
def prefixEnd_399747 : Nat := 4983230072969 + 3 ^ 40 * 399747 * 2
def baseEnd_399747 : Nat := 7602309303442693397189

theorem tailTrace_399747 : CollatzResearch.WordTrace tailWord_399747 prefixEnd_399747 7602309303442693397189 := by
  unfold tailWord_399747
  simp only [CollatzResearch.WordTrace]
  refine ⟨14579970882792365197349495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9719980588528243464899663 14579970882792365197349495)
  ·
    refine ⟨21869956324188547796024243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14579970882792365197349495 21869956324188547796024243)
    ·
      refine ⟨32804934486282821694036365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21869956324188547796024243 32804934486282821694036365)
      ·
        refine ⟨12301850432356058135263637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32804934486282821694036365 12301850432356058135263637)
        ·
          refine ⟨576649239016690225090483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12301850432356058135263637 576649239016690225090483)
          ·
            refine ⟨864973858525035337635725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 576649239016690225090483 864973858525035337635725)
            ·
              refine ⟨324365196946888251613397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 864973858525035337635725 324365196946888251613397)
              ·
                refine ⟨7602309303442693397189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 324365196946888251613397 7602309303442693397189)
                ·
                  rfl

theorem cell23_399747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 7].length) (baseStart_399747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_399747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_399747 prefixEnd_399747 := by exact prefixLift 399747
  have htrace : WordTrace (prefixWord ++ tailWord_399747) baseStart_399747 baseEnd_399747 := by
    simpa [prefixWord, tailWord_399747, baseEnd_399747] using wordTrace_append hprefix tailTrace_399747
  have hstable : (prefixWord ++ tailWord_399747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399747).length < 2 ^ (prefixWord ++ tailWord_399747).sum := by decide
  have hdescent : baseEnd_399747 < baseStart_399747 := by decide
  rcases family_descends (prefixWord ++ tailWord_399747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399758 : List Nat := [4, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2]
def baseStart_399758 : Nat := 118140960795 + 399758 * 2 ^ 59
def prefixEnd_399758 : Nat := 4983230072969 + 3 ^ 40 * 399758 * 2
def baseEnd_399758 : Nat := 205267999480152178686553

theorem tailTrace_399758 : CollatzResearch.WordTrace tailWord_399758 prefixEnd_399758 205267999480152178686553 := by
  unfold tailWord_399758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1822546510719064259499991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9720248057168342717333285 1822546510719064259499991)
  ·
    refine ⟨2733819766078596389249987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1822546510719064259499991 2733819766078596389249987)
    ·
      refine ⟨4100729649117894583874981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2733819766078596389249987 4100729649117894583874981)
      ·
        refine ⟨768886809209605234476559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4100729649117894583874981 768886809209605234476559)
        ·
          refine ⟨1153330213814407851714839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 768886809209605234476559 1153330213814407851714839)
          ·
            refine ⟨1729995320721611777572259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1153330213814407851714839 1729995320721611777572259)
            ·
              refine ⟨2594992981082417666358389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1729995320721611777572259 2594992981082417666358389)
              ·
                refine ⟨243280591976476656221099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2594992981082417666358389 243280591976476656221099)
                ·
                  refine ⟨364920887964714984331649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 243280591976476656221099 364920887964714984331649)
                  ·
                    refine ⟨273690665973536238248737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 364920887964714984331649 273690665973536238248737)
                    ·
                      refine ⟨205267999480152178686553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 273690665973536238248737 205267999480152178686553)
                      ·
                        rfl

theorem cell23_399758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_399758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_399758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_399758 prefixEnd_399758 := by exact prefixLift 399758
  have htrace : WordTrace (prefixWord ++ tailWord_399758) baseStart_399758 baseEnd_399758 := by
    simpa [prefixWord, tailWord_399758, baseEnd_399758] using wordTrace_append hprefix tailTrace_399758
  have hstable : (prefixWord ++ tailWord_399758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399758).length < 2 ^ (prefixWord ++ tailWord_399758).sum := by decide
  have hdescent : baseEnd_399758 < baseStart_399758 := by decide
  rcases family_descends (prefixWord ++ tailWord_399758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399780 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 1, 5, 4]
def baseStart_399780 : Nat := 118140960795 + 399780 * 2 ^ 59
def prefixEnd_399780 : Nat := 4983230072969 + 3 ^ 40 * 399780 * 2
def baseEnd_399780 : Nat := 205279296054551092611451

theorem tailTrace_399780 : CollatzResearch.WordTrace tailWord_399780 prefixEnd_399780 205279296054551092611451 := by
  unfold tailWord_399780
  simp only [CollatzResearch.WordTrace]
  refine ⟨7290587245836405916650397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9720782994448541222200529 7290587245836405916650397)
  ·
    refine ⟨2733970217188652218743899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7290587245836405916650397 2733970217188652218743899)
    ·
      refine ⟨4100955325782978328115849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2733970217188652218743899 4100955325782978328115849)
      ·
        refine ⟨3075716494337233746086887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4100955325782978328115849 3075716494337233746086887)
        ·
          refine ⟨4613574741505850619130331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3075716494337233746086887 4613574741505850619130331)
          ·
            refine ⟨6920362112258775928695497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4613574741505850619130331 6920362112258775928695497)
            ·
              refine ⟨5190271584194081946521623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6920362112258775928695497 5190271584194081946521623)
              ·
                refine ⟨7785407376291122919782435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5190271584194081946521623 7785407376291122919782435)
                ·
                  refine ⟨11678111064436684379673653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7785407376291122919782435 11678111064436684379673653)
                  ·
                    refine ⟨1094822912290939160594405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11678111064436684379673653 1094822912290939160594405)
                    ·
                      refine ⟨205279296054551092611451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1094822912290939160594405 205279296054551092611451)
                      ·
                        rfl

theorem cell23_399780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_399780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_399780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_399780 prefixEnd_399780 := by exact prefixLift 399780
  have htrace : WordTrace (prefixWord ++ tailWord_399780) baseStart_399780 baseEnd_399780 := by
    simpa [prefixWord, tailWord_399780, baseEnd_399780] using wordTrace_append hprefix tailTrace_399780
  have hstable : (prefixWord ++ tailWord_399780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399780).length < 2 ^ (prefixWord ++ tailWord_399780).sum := by decide
  have hdescent : baseEnd_399780 < baseStart_399780 := by decide
  rcases family_descends (prefixWord ++ tailWord_399780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399800 : List Nat := [2, 1, 2, 1, 2, 2, 1, 4, 2, 1, 5]
def baseStart_399800 : Nat := 118140960795 + 399800 * 2 ^ 59
def prefixEnd_399800 : Nat := 4983230072969 + 3 ^ 40 * 399800 * 2
def baseEnd_399800 : Nat := 205289565667641014361359

theorem tailTrace_399800 : CollatzResearch.WordTrace tailWord_399800 prefixEnd_399800 205289565667641014361359 := by
  unfold tailWord_399800
  simp only [CollatzResearch.WordTrace]
  refine ⟨7290951975800177624514427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9721269301066903499352569 7290951975800177624514427)
  ·
    refine ⟨10936427963700266436771641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7290951975800177624514427 10936427963700266436771641)
    ·
      refine ⟨8202320972775199827578731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10936427963700266436771641 8202320972775199827578731)
      ·
        refine ⟨12303481459162799741368097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8202320972775199827578731 12303481459162799741368097)
        ·
          refine ⟨9227611094372099806026073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12303481459162799741368097 9227611094372099806026073)
          ·
            refine ⟨6920708320779074854519555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9227611094372099806026073 6920708320779074854519555)
            ·
              refine ⟨10381062481168612281779333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6920708320779074854519555 10381062481168612281779333)
              ·
                refine ⟨1946449215219114802833625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10381062481168612281779333 1946449215219114802833625)
                ·
                  refine ⟨1459836911414336102125219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1946449215219114802833625 1459836911414336102125219)
                  ·
                    refine ⟨2189755367121504153187829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1459836911414336102125219 2189755367121504153187829)
                    ·
                      refine ⟨205289565667641014361359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2189755367121504153187829 205289565667641014361359)
                      ·
                        rfl

theorem cell23_399800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 2, 1, 5].length) (baseStart_399800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_399800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_399800 prefixEnd_399800 := by exact prefixLift 399800
  have htrace : WordTrace (prefixWord ++ tailWord_399800) baseStart_399800 baseEnd_399800 := by
    simpa [prefixWord, tailWord_399800, baseEnd_399800] using wordTrace_append hprefix tailTrace_399800
  have hstable : (prefixWord ++ tailWord_399800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399800).length < 2 ^ (prefixWord ++ tailWord_399800).sum := by decide
  have hdescent : baseEnd_399800 < baseStart_399800 := by decide
  rcases family_descends (prefixWord ++ tailWord_399800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399801 : List Nat := [1, 2, 1, 4, 3, 2, 2, 2, 1, 3, 2]
def baseStart_399801 : Nat := 118140960795 + 399801 * 2 ^ 59
def prefixEnd_399801 : Nat := 4983230072969 + 3 ^ 40 * 399801 * 2
def baseEnd_399801 : Nat := 205290079148295510448855

theorem tailTrace_399801 : CollatzResearch.WordTrace tailWord_399801 prefixEnd_399801 205290079148295510448855 := by
  unfold tailWord_399801
  simp only [CollatzResearch.WordTrace]
  refine ⟨14581940424596732419815257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9721293616397821613210171 14581940424596732419815257)
  ·
    refine ⟨10936455318447549314861443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14581940424596732419815257 10936455318447549314861443)
    ·
      refine ⟨16404682977671323972292165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10936455318447549314861443 16404682977671323972292165)
      ·
        refine ⟨3075878058313373244804781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16404682977671323972292165 3075878058313373244804781)
        ·
          refine ⟨1153454271867514966801793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3075878058313373244804781 1153454271867514966801793)
          ·
            refine ⟨865090703900636225101345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1153454271867514966801793 865090703900636225101345)
            ·
              refine ⟨648818027925477168826009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 865090703900636225101345 648818027925477168826009)
              ·
                refine ⟨486613520944107876619507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 648818027925477168826009 486613520944107876619507)
                ·
                  refine ⟨729920281416161814929261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 486613520944107876619507 729920281416161814929261)
                  ·
                    refine ⟨273720105531060680598473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 729920281416161814929261 273720105531060680598473)
                    ·
                      refine ⟨205290079148295510448855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 273720105531060680598473 205290079148295510448855)
                      ·
                        rfl

theorem cell23_399801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2, 1, 3, 2].length) (baseStart_399801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_399801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_399801 prefixEnd_399801 := by exact prefixLift 399801
  have htrace : WordTrace (prefixWord ++ tailWord_399801) baseStart_399801 baseEnd_399801 := by
    simpa [prefixWord, tailWord_399801, baseEnd_399801] using wordTrace_append hprefix tailTrace_399801
  have hstable : (prefixWord ++ tailWord_399801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399801).length < 2 ^ (prefixWord ++ tailWord_399801).sum := by decide
  have hdescent : baseEnd_399801 < baseStart_399801 := by decide
  rcases family_descends (prefixWord ++ tailWord_399801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399809 : List Nat := [1, 2, 7, 1, 1, 2, 1, 3, 1, 2, 2]
def baseStart_399809 : Nat := 118140960795 + 399809 * 2 ^ 59
def prefixEnd_399809 : Nat := 4983230072969 + 3 ^ 40 * 399809 * 2
def baseEnd_399809 : Nat := 205294186993531479148819

theorem tailTrace_399809 : CollatzResearch.WordTrace tailWord_399809 prefixEnd_399809 205294186993531479148819 := by
  unfold tailWord_399809
  simp only [CollatzResearch.WordTrace]
  refine ⟨14582232208567749786106481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9721488139045166524070987 14582232208567749786106481)
  ·
    refine ⟨10936674156425812339579861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14582232208567749786106481 10936674156425812339579861)
    ·
      refine ⟨256328300541229976708903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 10936674156425812339579861 256328300541229976708903)
      ·
        refine ⟨384492450811844965063355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256328300541229976708903 384492450811844965063355)
        ·
          refine ⟨576738676217767447595033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384492450811844965063355 576738676217767447595033)
          ·
            refine ⟨432554007163325585696275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 576738676217767447595033 432554007163325585696275)
            ·
              refine ⟨648831010744988378544413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432554007163325585696275 648831010744988378544413)
              ·
                refine ⟨243311629029370641954155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 648831010744988378544413 243311629029370641954155)
                ·
                  refine ⟨364967443544055962931233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 243311629029370641954155 364967443544055962931233)
                  ·
                    refine ⟨273725582658041972198425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 364967443544055962931233 273725582658041972198425)
                    ·
                      refine ⟨205294186993531479148819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 273725582658041972198425 205294186993531479148819)
                      ·
                        rfl

theorem cell23_399809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_399809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_399809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_399809 prefixEnd_399809 := by exact prefixLift 399809
  have htrace : WordTrace (prefixWord ++ tailWord_399809) baseStart_399809 baseEnd_399809 := by
    simpa [prefixWord, tailWord_399809, baseEnd_399809] using wordTrace_append hprefix tailTrace_399809
  have hstable : (prefixWord ++ tailWord_399809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399809).length < 2 ^ (prefixWord ++ tailWord_399809).sum := by decide
  have hdescent : baseEnd_399809 < baseStart_399809 := by decide
  rcases family_descends (prefixWord ++ tailWord_399809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399842 : List Nat := [3, 3, 3, 2, 1, 2, 2, 1, 2, 1, 3]
def baseStart_399842 : Nat := 118140960795 + 399842 * 2 ^ 59
def prefixEnd_399842 : Nat := 4983230072969 + 3 ^ 40 * 399842 * 2
def baseEnd_399842 : Nat := 205311131855129850036167

theorem tailTrace_399842 : CollatzResearch.WordTrace tailWord_399842 prefixEnd_399842 205311131855129850036167 := by
  unfold tailWord_399842
  simp only [CollatzResearch.WordTrace]
  refine ⟨3645858954362049105514445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9722290544965464281371853 3645858954362049105514445)
  ·
    refine ⟨1367197107885768414567917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3645858954362049105514445 1367197107885768414567917)
    ·
      refine ⟨512698915457163155462969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1367197107885768414567917 512698915457163155462969)
      ·
        refine ⟨384524186592872366597227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 512698915457163155462969 384524186592872366597227)
        ·
          refine ⟨576786279889308549895841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384524186592872366597227 576786279889308549895841)
          ·
            refine ⟨432589709916981412421881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 576786279889308549895841 432589709916981412421881)
            ·
              refine ⟨324442282437736059316411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 432589709916981412421881 324442282437736059316411)
              ·
                refine ⟨486663423656604088974617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 324442282437736059316411 486663423656604088974617)
                ·
                  refine ⟨364997567742453066730963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 486663423656604088974617 364997567742453066730963)
                  ·
                    refine ⟨547496351613679600096445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 364997567742453066730963 547496351613679600096445)
                    ·
                      refine ⟨205311131855129850036167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 547496351613679600096445 205311131855129850036167)
                      ·
                        rfl

theorem cell23_399842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_399842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_399842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_399842 prefixEnd_399842 := by exact prefixLift 399842
  have htrace : WordTrace (prefixWord ++ tailWord_399842) baseStart_399842 baseEnd_399842 := by
    simpa [prefixWord, tailWord_399842, baseEnd_399842] using wordTrace_append hprefix tailTrace_399842
  have hstable : (prefixWord ++ tailWord_399842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399842).length < 2 ^ (prefixWord ++ tailWord_399842).sum := by decide
  have hdescent : baseEnd_399842 < baseStart_399842 := by decide
  rcases family_descends (prefixWord ++ tailWord_399842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399847 : List Nat := [1, 1, 5, 2, 1, 1, 2, 1, 1, 5, 3]
def baseStart_399847 : Nat := 118140960795 + 399847 * 2 ^ 59
def prefixEnd_399847 : Nat := 4983230072969 + 3 ^ 40 * 399847 * 2
def baseEnd_399847 : Nat := 205313699258402330473643

theorem tailTrace_399847 : CollatzResearch.WordTrace tailWord_399847 prefixEnd_399847 205313699258402330473643 := by
  unfold tailWord_399847
  simp only [CollatzResearch.WordTrace]
  refine ⟨14583618182430082275989795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9722412121620054850659863 14583618182430082275989795)
  ·
    refine ⟨21875427273645123413984693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14583618182430082275989795 21875427273645123413984693)
    ·
      refine ⟨2050821306904230320061065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21875427273645123413984693 2050821306904230320061065)
      ·
        refine ⟨1538115980178172740045799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2050821306904230320061065 1538115980178172740045799)
        ·
          refine ⟨2307173970267259110068699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1538115980178172740045799 2307173970267259110068699)
          ·
            refine ⟨3460760955400888665103049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2307173970267259110068699 3460760955400888665103049)
            ·
              refine ⟨2595570716550666498827287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3460760955400888665103049 2595570716550666498827287)
              ·
                refine ⟨3893356074825999748240931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2595570716550666498827287 3893356074825999748240931)
                ·
                  refine ⟨5840034112238999622361397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3893356074825999748240931 5840034112238999622361397)
                  ·
                    refine ⟨547503198022406214596381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5840034112238999622361397 547503198022406214596381)
                    ·
                      refine ⟨205313699258402330473643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 547503198022406214596381 205313699258402330473643)
                      ·
                        rfl

theorem cell23_399847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_399847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_399847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_399847 prefixEnd_399847 := by exact prefixLift 399847
  have htrace : WordTrace (prefixWord ++ tailWord_399847) baseStart_399847 baseEnd_399847 := by
    simpa [prefixWord, tailWord_399847, baseEnd_399847] using wordTrace_append hprefix tailTrace_399847
  have hstable : (prefixWord ++ tailWord_399847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399847).length < 2 ^ (prefixWord ++ tailWord_399847).sum := by decide
  have hdescent : baseEnd_399847 < baseStart_399847 := by decide
  rcases family_descends (prefixWord ++ tailWord_399847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399848 : List Nat := [2, 1, 4, 1, 1, 3, 4, 1, 2, 2, 2]
def baseStart_399848 : Nat := 118140960795 + 399848 * 2 ^ 59
def prefixEnd_399848 : Nat := 4983230072969 + 3 ^ 40 * 399848 * 2
def baseEnd_399848 : Nat := 205314212739056826561139

theorem tailTrace_399848 : CollatzResearch.WordTrace tailWord_399848 prefixEnd_399848 205314212739056826561139 := by
  unfold tailWord_399848
  simp only [CollatzResearch.WordTrace]
  refine ⟨7291827327713229723388099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9722436436950972964517465 7291827327713229723388099)
  ·
    refine ⟨10937740991569844585082149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7291827327713229723388099 10937740991569844585082149)
    ·
      refine ⟨2050826435919345859702903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10937740991569844585082149 2050826435919345859702903)
      ·
        refine ⟨3076239653879018789554355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2050826435919345859702903 3076239653879018789554355)
        ·
          refine ⟨4614359480818528184331533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3076239653879018789554355 4614359480818528184331533)
          ·
            refine ⟨1730384805306948069124325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4614359480818528184331533 1730384805306948069124325)
            ·
              refine ⟨324447150995052762960811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1730384805306948069124325 324447150995052762960811)
              ·
                refine ⟨486670726492579144441217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 324447150995052762960811 486670726492579144441217)
                ·
                  refine ⟨365003044869434358330913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 486670726492579144441217 365003044869434358330913)
                  ·
                    refine ⟨273752283652075768748185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 365003044869434358330913 273752283652075768748185)
                    ·
                      refine ⟨205314212739056826561139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 273752283652075768748185 205314212739056826561139)
                      ·
                        rfl

theorem cell23_399848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 1, 2, 2, 2].length) (baseStart_399848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_399848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_399848 prefixEnd_399848 := by exact prefixLift 399848
  have htrace : WordTrace (prefixWord ++ tailWord_399848) baseStart_399848 baseEnd_399848 := by
    simpa [prefixWord, tailWord_399848, baseEnd_399848] using wordTrace_append hprefix tailTrace_399848
  have hstable : (prefixWord ++ tailWord_399848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399848).length < 2 ^ (prefixWord ++ tailWord_399848).sum := by decide
  have hdescent : baseEnd_399848 < baseStart_399848 := by decide
  rcases family_descends (prefixWord ++ tailWord_399848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399914 : List Nat := [3, 1, 4, 1, 1, 2, 1, 1, 5, 4]
def baseStart_399914 : Nat := 118140960795 + 399914 * 2 ^ 59
def prefixEnd_399914 : Nat := 4983230072969 + 3 ^ 40 * 399914 * 2
def baseEnd_399914 : Nat := 68449367487417856111945

theorem tailTrace_399914 : CollatzResearch.WordTrace tailWord_399914 prefixEnd_399914 68449367487417856111945 := by
  unfold tailWord_399914
  simp only [CollatzResearch.WordTrace]
  refine ⟨3646515468296838179669699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9724041248791568479119197 3646515468296838179669699)
  ·
    refine ⟨5469773202445257269504549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3646515468296838179669699 5469773202445257269504549)
    ·
      refine ⟨1025582475458485738032103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5469773202445257269504549 1025582475458485738032103)
      ·
        refine ⟨1538373713187728607048155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1025582475458485738032103 1538373713187728607048155)
        ·
          refine ⟨2307560569781592910572233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1538373713187728607048155 2307560569781592910572233)
          ·
            refine ⟨1730670427336194682929175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2307560569781592910572233 1730670427336194682929175)
            ·
              refine ⟨2596005641004292024393763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1730670427336194682929175 2596005641004292024393763)
              ·
                refine ⟨3894008461506438036590645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2596005641004292024393763 3894008461506438036590645)
                ·
                  refine ⟨365063293266228565930373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3894008461506438036590645 365063293266228565930373)
                  ·
                    refine ⟨68449367487417856111945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 365063293266228565930373 68449367487417856111945)
                    ·
                      rfl

theorem cell23_399914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_399914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_399914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_399914 prefixEnd_399914 := by exact prefixLift 399914
  have htrace : WordTrace (prefixWord ++ tailWord_399914) baseStart_399914 baseEnd_399914 := by
    simpa [prefixWord, tailWord_399914, baseEnd_399914] using wordTrace_append hprefix tailTrace_399914
  have hstable : (prefixWord ++ tailWord_399914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399914).length < 2 ^ (prefixWord ++ tailWord_399914).sum := by decide
  have hdescent : baseEnd_399914 < baseStart_399914 := by decide
  rcases family_descends (prefixWord ++ tailWord_399914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399918 : List Nat := [4, 1, 3, 1, 4, 1, 1, 1, 2, 5]
def baseStart_399918 : Nat := 118140960795 + 399918 * 2 ^ 59
def prefixEnd_399918 : Nat := 4983230072969 + 3 ^ 40 * 399918 * 2
def baseEnd_399918 : Nat := 68450052128290517561939

theorem tailTrace_399918 : CollatzResearch.WordTrace tailWord_399918 prefixEnd_399918 68450052128290517561939 := by
  unfold tailWord_399918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1823275970646607675228051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9724138510115240934549605 1823275970646607675228051)
  ·
    refine ⟨2734913955969911512842077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1823275970646607675228051 2734913955969911512842077)
    ·
      refine ⟨1025592733488716817315779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2734913955969911512842077 1025592733488716817315779)
      ·
        refine ⟨1538389100233075225973669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1025592733488716817315779 1538389100233075225973669)
        ·
          refine ⟨288447956293701604870063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1538389100233075225973669 288447956293701604870063)
          ·
            refine ⟨432671934440552407305095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288447956293701604870063 432671934440552407305095)
            ·
              refine ⟨649007901660828610957643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432671934440552407305095 649007901660828610957643)
              ·
                refine ⟨973511852491242916436465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 649007901660828610957643 973511852491242916436465)
                ·
                  refine ⟨730133889368432187327349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 973511852491242916436465 730133889368432187327349)
                  ·
                    refine ⟨68450052128290517561939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 730133889368432187327349 68450052128290517561939)
                    ·
                      rfl

theorem cell23_399918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_399918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_399918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_399918 prefixEnd_399918 := by exact prefixLift 399918
  have htrace : WordTrace (prefixWord ++ tailWord_399918) baseStart_399918 baseEnd_399918 := by
    simpa [prefixWord, tailWord_399918, baseEnd_399918] using wordTrace_append hprefix tailTrace_399918
  have hstable : (prefixWord ++ tailWord_399918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399918).length < 2 ^ (prefixWord ++ tailWord_399918).sum := by decide
  have hdescent : baseEnd_399918 < baseStart_399918 := by decide
  rcases family_descends (prefixWord ++ tailWord_399918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399957 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 5, 5]
def baseStart_399957 : Nat := 118140960795 + 399957 * 2 ^ 59
def prefixEnd_399957 : Nat := 4983230072969 + 3 ^ 40 * 399957 * 2
def baseEnd_399957 : Nat := 68456727376798966699379

theorem tailTrace_399957 : CollatzResearch.WordTrace tailWord_399957 prefixEnd_399957 68456727376798966699379 := by
  unfold tailWord_399957
  simp only [CollatzResearch.WordTrace]
  refine ⟨14587630212031571062494125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9725086808021047374996083 14587630212031571062494125)
  ·
    refine ⟨5470361329511839148435297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14587630212031571062494125 5470361329511839148435297)
    ·
      refine ⟨4102770997133879361326473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5470361329511839148435297 4102770997133879361326473)
      ·
        refine ⟨3077078247850409520994855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4102770997133879361326473 3077078247850409520994855)
        ·
          refine ⟨4615617371775614281492283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3077078247850409520994855 4615617371775614281492283)
          ·
            refine ⟨6923426057663421422238425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4615617371775614281492283 6923426057663421422238425)
            ·
              refine ⟨5192569543247566066678819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6923426057663421422238425 5192569543247566066678819)
              ·
                refine ⟨7788854314871349100018229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5192569543247566066678819 7788854314871349100018229)
                ·
                  refine ⟨730205092019188978126709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7788854314871349100018229 730205092019188978126709)
                  ·
                    refine ⟨68456727376798966699379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 730205092019188978126709 68456727376798966699379)
                    ·
                      rfl

theorem cell23_399957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_399957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_399957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_399957 prefixEnd_399957 := by exact prefixLift 399957
  have htrace : WordTrace (prefixWord ++ tailWord_399957) baseStart_399957 baseEnd_399957 := by
    simpa [prefixWord, tailWord_399957, baseEnd_399957] using wordTrace_append hprefix tailTrace_399957
  have hstable : (prefixWord ++ tailWord_399957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399957).length < 2 ^ (prefixWord ++ tailWord_399957).sum := by decide
  have hdescent : baseEnd_399957 < baseStart_399957 := by decide
  rcases family_descends (prefixWord ++ tailWord_399957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399981 : List Nat := [1, 5, 1, 1, 3, 1, 2, 1, 1, 5, 2]
def baseStart_399981 : Nat := 118140960795 + 399981 * 2 ^ 59
def prefixEnd_399981 : Nat := 4983230072969 + 3 ^ 40 * 399981 * 2
def baseEnd_399981 : Nat := 205382505666104806198027

theorem tailTrace_399981 : CollatzResearch.WordTrace tailWord_399981 prefixEnd_399981 205382505666104806198027 := by
  unfold tailWord_399981
  simp only [CollatzResearch.WordTrace]
  refine ⟨14588505563944623161367797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9725670375963082107578531 14588505563944623161367797)
  ·
    refine ⟨1367672396619808421378231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14588505563944623161367797 1367672396619808421378231)
    ·
      refine ⟨2051508594929712632067347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1367672396619808421378231 2051508594929712632067347)
      ·
        refine ⟨3077262892394568948101021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2051508594929712632067347 3077262892394568948101021)
        ·
          refine ⟨1153973584647963355537883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3077262892394568948101021 1153973584647963355537883)
          ·
            refine ⟨1730960376971945033306825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1153973584647963355537883 1730960376971945033306825)
            ·
              refine ⟨1298220282728958774980119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1730960376971945033306825 1298220282728958774980119)
              ·
                refine ⟨1947330424093438162470179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1298220282728958774980119 1947330424093438162470179)
                ·
                  refine ⟨2920995636140157243705269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1947330424093438162470179 2920995636140157243705269)
                  ·
                    refine ⟨273843340888139741597369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2920995636140157243705269 273843340888139741597369)
                    ·
                      refine ⟨205382505666104806198027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 273843340888139741597369 205382505666104806198027)
                      ·
                        rfl

theorem cell23_399981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 5, 2].length) (baseStart_399981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_399981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_399981 prefixEnd_399981 := by exact prefixLift 399981
  have htrace : WordTrace (prefixWord ++ tailWord_399981) baseStart_399981 baseEnd_399981 := by
    simpa [prefixWord, tailWord_399981, baseEnd_399981] using wordTrace_append hprefix tailTrace_399981
  have hstable : (prefixWord ++ tailWord_399981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399981).length < 2 ^ (prefixWord ++ tailWord_399981).sum := by decide
  have hdescent : baseEnd_399981 < baseStart_399981 := by decide
  rcases family_descends (prefixWord ++ tailWord_399981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400005 : List Nat := [1, 3, 1, 1, 4, 3, 3, 2, 1, 1, 3]
def baseStart_400005 : Nat := 118140960795 + 400005 * 2 ^ 59
def prefixEnd_400005 : Nat := 4983230072969 + 3 ^ 40 * 400005 * 2
def baseEnd_400005 : Nat := 205394829201812712297917

theorem tailTrace_400005 : CollatzResearch.WordTrace tailWord_400005 prefixEnd_400005 205394829201812712297917 := by
  unfold tailWord_400005
  simp only [CollatzResearch.WordTrace]
  refine ⟨14589380915857675260241469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9726253943905116840160979 14589380915857675260241469)
  ·
    refine ⟨5471017843446628222590551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14589380915857675260241469 5471017843446628222590551)
    ·
      refine ⟨8206526765169942333885827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5471017843446628222590551 8206526765169942333885827)
      ·
        refine ⟨12309790147754913500828741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8206526765169942333885827 12309790147754913500828741)
        ·
          refine ⟨2308085652704046281405389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12309790147754913500828741 2308085652704046281405389)
          ·
            refine ⟨865532119764017355527021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2308085652704046281405389 865532119764017355527021)
            ·
              refine ⟨324574544911506508322633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 865532119764017355527021 324574544911506508322633)
              ·
                refine ⟨243430908683629881241975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 324574544911506508322633 243430908683629881241975)
                ·
                  refine ⟨365146363025444821862963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 243430908683629881241975 365146363025444821862963)
                  ·
                    refine ⟨547719544538167232794445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 365146363025444821862963 547719544538167232794445)
                    ·
                      refine ⟨205394829201812712297917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 547719544538167232794445 205394829201812712297917)
                      ·
                        rfl

theorem cell23_400005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 2, 1, 1, 3].length) (baseStart_400005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400005 prefixEnd_400005 := by exact prefixLift 400005
  have htrace : WordTrace (prefixWord ++ tailWord_400005) baseStart_400005 baseEnd_400005 := by
    simpa [prefixWord, tailWord_400005, baseEnd_400005] using wordTrace_append hprefix tailTrace_400005
  have hstable : (prefixWord ++ tailWord_400005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400005).length < 2 ^ (prefixWord ++ tailWord_400005).sum := by decide
  have hdescent : baseEnd_400005 < baseStart_400005 := by decide
  rcases family_descends (prefixWord ++ tailWord_400005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400007 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 6]
def baseStart_400007 : Nat := 118140960795 + 400007 * 2 ^ 59
def prefixEnd_400007 : Nat := 4983230072969 + 3 ^ 40 * 400007 * 2
def baseEnd_400007 : Nat := 205395856163121704472907

theorem tailTrace_400007 : CollatzResearch.WordTrace tailWord_400007 prefixEnd_400007 205395856163121704472907 := by
  unfold tailWord_400007
  simp only [CollatzResearch.WordTrace]
  refine ⟨14589453861850429601814275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9726302574566953067876183 14589453861850429601814275)
  ·
    refine ⟨21884180792775644402721413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14589453861850429601814275 21884180792775644402721413)
    ·
      refine ⟨4103283898645433325510265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21884180792775644402721413 4103283898645433325510265)
      ·
        refine ⟨3077462923984074994132699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4103283898645433325510265 3077462923984074994132699)
        ·
          refine ⟨4616194385976112491199049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3077462923984074994132699 4616194385976112491199049)
          ·
            refine ⟨3462145789482084368399287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4616194385976112491199049 3462145789482084368399287)
            ·
              refine ⟨5193218684223126552598931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3462145789482084368399287 5193218684223126552598931)
              ·
                refine ⟨7789828026334689828898397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5193218684223126552598931 7789828026334689828898397)
                ·
                  refine ⟨2921185509875508685836899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7789828026334689828898397 2921185509875508685836899)
                  ·
                    refine ⟨4381778264813263028755349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2921185509875508685836899 4381778264813263028755349)
                    ·
                      refine ⟨205395856163121704472907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4381778264813263028755349 205395856163121704472907)
                      ·
                        rfl

theorem cell23_400007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_400007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400007 prefixEnd_400007 := by exact prefixLift 400007
  have htrace : WordTrace (prefixWord ++ tailWord_400007) baseStart_400007 baseEnd_400007 := by
    simpa [prefixWord, tailWord_400007, baseEnd_400007] using wordTrace_append hprefix tailTrace_400007
  have hstable : (prefixWord ++ tailWord_400007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400007).length < 2 ^ (prefixWord ++ tailWord_400007).sum := by decide
  have hdescent : baseEnd_400007 < baseStart_400007 := by decide
  rcases family_descends (prefixWord ++ tailWord_400007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400011 : List Nat := [1, 1, 1, 1, 4, 1, 2, 5, 3, 2, 2]
def baseStart_400011 : Nat := 118140960795 + 400011 * 2 ^ 59
def prefixEnd_400011 : Nat := 4983230072969 + 3 ^ 40 * 400011 * 2
def baseEnd_400011 : Nat := 205397910085739688822889

theorem tailTrace_400011 : CollatzResearch.WordTrace tailWord_400011 prefixEnd_400011 205397910085739688822889 := by
  unfold tailWord_400011
  simp only [CollatzResearch.WordTrace]
  refine ⟨14589599753835938284959887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9726399835890625523306591 14589599753835938284959887)
  ·
    refine ⟨21884399630753907427439831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14589599753835938284959887 21884399630753907427439831)
    ·
      refine ⟨32826599446130861141159747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21884399630753907427439831 32826599446130861141159747)
      ·
        refine ⟨49239899169196291711739621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32826599446130861141159747 49239899169196291711739621)
        ·
          refine ⟨9232481094224304695951179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49239899169196291711739621 9232481094224304695951179)
          ·
            refine ⟨13848721641336457043926769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9232481094224304695951179 13848721641336457043926769)
            ·
              refine ⟨10386541231002342782945077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13848721641336457043926769 10386541231002342782945077)
              ·
                refine ⟨973738240406469635901101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10386541231002342782945077 973738240406469635901101)
                ·
                  refine ⟨365151840152426113462913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 973738240406469635901101 365151840152426113462913)
                  ·
                    refine ⟨273863880114319585097185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 365151840152426113462913 273863880114319585097185)
                    ·
                      refine ⟨205397910085739688822889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 273863880114319585097185 205397910085739688822889)
                      ·
                        rfl

theorem cell23_400011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 3, 2, 2].length) (baseStart_400011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400011 prefixEnd_400011 := by exact prefixLift 400011
  have htrace : WordTrace (prefixWord ++ tailWord_400011) baseStart_400011 baseEnd_400011 := by
    simpa [prefixWord, tailWord_400011, baseEnd_400011] using wordTrace_append hprefix tailTrace_400011
  have hstable : (prefixWord ++ tailWord_400011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400011).length < 2 ^ (prefixWord ++ tailWord_400011).sum := by decide
  have hdescent : baseEnd_400011 < baseStart_400011 := by decide
  rcases family_descends (prefixWord ++ tailWord_400011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400014 : List Nat := [4, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5]
def baseStart_400014 : Nat := 118140960795 + 400014 * 2 ^ 59
def prefixEnd_400014 : Nat := 4983230072969 + 3 ^ 40 * 400014 * 2
def baseEnd_400014 : Nat := 205399450527703177085375

theorem tailTrace_400014 : CollatzResearch.WordTrace tailWord_400014 prefixEnd_400014 205399450527703177085375 := by
  unfold tailWord_400014
  simp only [CollatzResearch.WordTrace]
  refine ⟨1823713646603133724664887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9726472781883379864879397 1823713646603133724664887)
  ·
    refine ⟨2735570469904700586997331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1823713646603133724664887 2735570469904700586997331)
    ·
      refine ⟨4103355704857050880495997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2735570469904700586997331 4103355704857050880495997)
      ·
        refine ⟨1538758389321394080185999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4103355704857050880495997 1538758389321394080185999)
        ·
          refine ⟨2308137583982091120278999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1538758389321394080185999 2308137583982091120278999)
          ·
            refine ⟨3462206375973136680418499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2308137583982091120278999 3462206375973136680418499)
            ·
              refine ⟨5193309563959705020627749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3462206375973136680418499 5193309563959705020627749)
              ·
                refine ⟨973745543242444691367703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5193309563959705020627749 973745543242444691367703)
                ·
                  refine ⟨1460618314863667037051555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 973745543242444691367703 1460618314863667037051555)
                  ·
                    refine ⟨2190927472295500555577333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1460618314863667037051555 2190927472295500555577333)
                    ·
                      refine ⟨205399450527703177085375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2190927472295500555577333 205399450527703177085375)
                      ·
                        rfl

theorem cell23_400014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_400014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400014 prefixEnd_400014 := by exact prefixLift 400014
  have htrace : WordTrace (prefixWord ++ tailWord_400014) baseStart_400014 baseEnd_400014 := by
    simpa [prefixWord, tailWord_400014, baseEnd_400014] using wordTrace_append hprefix tailTrace_400014
  have hstable : (prefixWord ++ tailWord_400014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400014).length < 2 ^ (prefixWord ++ tailWord_400014).sum := by decide
  have hdescent : baseEnd_400014 < baseStart_400014 := by decide
  rcases family_descends (prefixWord ++ tailWord_400014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400024 : List Nat := [2, 1, 2, 4, 1, 1, 2, 3, 1, 2, 4]
def baseStart_400024 : Nat := 118140960795 + 400024 * 2 ^ 59
def prefixEnd_400024 : Nat := 4983230072969 + 3 ^ 40 * 400024 * 2
def baseEnd_400024 : Nat := 205404585334248137960329

theorem tailTrace_400024 : CollatzResearch.WordTrace tailWord_400024 prefixEnd_400024 205404585334248137960329 := by
  unfold tailWord_400024
  simp only [CollatzResearch.WordTrace]
  refine ⟨7295036951394420752591563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9726715935192561003455417 7295036951394420752591563)
  ·
    refine ⟨10942555427091631128887345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7295036951394420752591563 10942555427091631128887345)
    ·
      refine ⟨8206916570318723346665509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10942555427091631128887345 8206916570318723346665509)
      ·
        refine ⟨1538796856934760627499783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8206916570318723346665509 1538796856934760627499783)
        ·
          refine ⟨2308195285402140941249675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1538796856934760627499783 2308195285402140941249675)
          ·
            refine ⟨3462292928103211411874513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2308195285402140941249675 3462292928103211411874513)
            ·
              refine ⟨2596719696077408558905885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3462292928103211411874513 2596719696077408558905885)
              ·
                refine ⟨973769886029028209589707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2596719696077408558905885 973769886029028209589707)
                ·
                  refine ⟨1460654829043542314384561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 973769886029028209589707 1460654829043542314384561)
                  ·
                    refine ⟨1095491121782656735788421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1460654829043542314384561 1095491121782656735788421)
                    ·
                      refine ⟨205404585334248137960329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1095491121782656735788421 205404585334248137960329)
                      ·
                        rfl

theorem cell23_400024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_400024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400024 prefixEnd_400024 := by exact prefixLift 400024
  have htrace : WordTrace (prefixWord ++ tailWord_400024) baseStart_400024 baseEnd_400024 := by
    simpa [prefixWord, tailWord_400024, baseEnd_400024] using wordTrace_append hprefix tailTrace_400024
  have hstable : (prefixWord ++ tailWord_400024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400024).length < 2 ^ (prefixWord ++ tailWord_400024).sum := by decide
  have hdescent : baseEnd_400024 < baseStart_400024 := by decide
  rcases family_descends (prefixWord ++ tailWord_400024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400028 : List Nat := [2, 2, 3, 2, 2, 3, 1, 2, 1, 1, 4]
def baseStart_400028 : Nat := 118140960795 + 400028 * 2 ^ 59
def prefixEnd_400028 : Nat := 4983230072969 + 3 ^ 40 * 400028 * 2
def baseEnd_400028 : Nat := 205406639256866122310311

theorem tailTrace_400028 : CollatzResearch.WordTrace tailWord_400028 prefixEnd_400028 205406639256866122310311 := by
  unfold tailWord_400028
  simp only [CollatzResearch.WordTrace]
  refine ⟨7295109897387175094164369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9726813196516233458885825 7295109897387175094164369)
  ·
    refine ⟨5471332423040381320623277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7295109897387175094164369 5471332423040381320623277)
    ·
      refine ⟨2051749658640142995233729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5471332423040381320623277 2051749658640142995233729)
      ·
        refine ⟨1538812243980107246425297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2051749658640142995233729 1538812243980107246425297)
        ·
          refine ⟨1154109182985080434818973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1538812243980107246425297 1154109182985080434818973)
          ·
            refine ⟨432790943619405163057115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1154109182985080434818973 432790943619405163057115)
            ·
              refine ⟨649186415429107744585673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432790943619405163057115 649186415429107744585673)
              ·
                refine ⟨486889811571830808439255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 649186415429107744585673 486889811571830808439255)
                ·
                  refine ⟨730334717357746212658883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 486889811571830808439255 730334717357746212658883)
                  ·
                    refine ⟨1095502076036619318988325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 730334717357746212658883 1095502076036619318988325)
                    ·
                      refine ⟨205406639256866122310311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1095502076036619318988325 205406639256866122310311)
                      ·
                        rfl

theorem cell23_400028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_400028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400028 prefixEnd_400028 := by exact prefixLift 400028
  have htrace : WordTrace (prefixWord ++ tailWord_400028) baseStart_400028 baseEnd_400028 := by
    simpa [prefixWord, tailWord_400028, baseEnd_400028] using wordTrace_append hprefix tailTrace_400028
  have hstable : (prefixWord ++ tailWord_400028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400028).length < 2 ^ (prefixWord ++ tailWord_400028).sum := by decide
  have hdescent : baseEnd_400028 < baseStart_400028 := by decide
  rcases family_descends (prefixWord ++ tailWord_400028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400078 : List Nat := [4, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3]
def baseStart_400078 : Nat := 118140960795 + 400078 * 2 ^ 59
def prefixEnd_400078 : Nat := 4983230072969 + 3 ^ 40 * 400078 * 2
def baseEnd_400078 : Nat := 205432313289590926685081

theorem tailTrace_400078 : CollatzResearch.WordTrace tailWord_400078 prefixEnd_400078 205432313289590926685081 := by
  unfold tailWord_400078
  simp only [CollatzResearch.WordTrace]
  refine ⟨1824005430574151090956111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9728028963062139151765925 1824005430574151090956111)
  ·
    refine ⟨2736008145861226636434167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1824005430574151090956111 2736008145861226636434167)
    ·
      refine ⟨4104012218791839954651251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2736008145861226636434167 4104012218791839954651251)
      ·
        refine ⟨6156018328187759931976877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4104012218791839954651251 6156018328187759931976877)
        ·
          refine ⟨2308506873070409974491329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6156018328187759931976877 2308506873070409974491329)
          ·
            refine ⟨1731380154802807480868497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2308506873070409974491329 1731380154802807480868497)
            ·
              refine ⟨1298535116102105610651373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1731380154802807480868497 1298535116102105610651373)
              ·
                refine ⟨486950668538289603994265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1298535116102105610651373 486950668538289603994265)
                ·
                  refine ⟨365213001403717202995699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 486950668538289603994265 365213001403717202995699)
                  ·
                    refine ⟨547819502105575804493549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 365213001403717202995699 547819502105575804493549)
                    ·
                      refine ⟨205432313289590926685081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 547819502105575804493549 205432313289590926685081)
                      ·
                        rfl

theorem cell23_400078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3].length) (baseStart_400078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400078 prefixEnd_400078 := by exact prefixLift 400078
  have htrace : WordTrace (prefixWord ++ tailWord_400078) baseStart_400078 baseEnd_400078 := by
    simpa [prefixWord, tailWord_400078, baseEnd_400078] using wordTrace_append hprefix tailTrace_400078
  have hstable : (prefixWord ++ tailWord_400078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400078).length < 2 ^ (prefixWord ++ tailWord_400078).sum := by decide
  have hdescent : baseEnd_400078 < baseStart_400078 := by decide
  rcases family_descends (prefixWord ++ tailWord_400078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400107 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 11]
def baseStart_400107 : Nat := 118140960795 + 400107 * 2 ^ 59
def prefixEnd_400107 : Nat := 4983230072969 + 3 ^ 40 * 400107 * 2
def baseEnd_400107 : Nat := 22827467136507923691383

theorem tailTrace_400107 : CollatzResearch.WordTrace tailWord_400107 prefixEnd_400107 22827467136507923691383 := by
  unfold tailWord_400107
  simp only [CollatzResearch.WordTrace]
  refine ⟨14593101161488146680454575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9728734107658764453636383 14593101161488146680454575)
  ·
    refine ⟨21889651742232220020681863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14593101161488146680454575 21889651742232220020681863)
    ·
      refine ⟨32834477613348330031022795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21889651742232220020681863 32834477613348330031022795)
      ·
        refine ⟨49251716420022495046534193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32834477613348330031022795 49251716420022495046534193)
        ·
          refine ⟨36938787315016871284900645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49251716420022495046534193 36938787315016871284900645)
          ·
            refine ⟨6926022621565663365918871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36938787315016871284900645 6926022621565663365918871)
            ·
              refine ⟨10389033932348495048878307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6926022621565663365918871 10389033932348495048878307)
              ·
                refine ⟨15583550898522742573317461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10389033932348495048878307 15583550898522742573317461)
                ·
                  refine ⟨22827467136507923691383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 15583550898522742573317461 22827467136507923691383)
                  ·
                    rfl

theorem cell23_400107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 11].length) (baseStart_400107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400107 prefixEnd_400107 := by exact prefixLift 400107
  have htrace : WordTrace (prefixWord ++ tailWord_400107) baseStart_400107 baseEnd_400107 := by
    simpa [prefixWord, tailWord_400107, baseEnd_400107] using wordTrace_append hprefix tailTrace_400107
  have hstable : (prefixWord ++ tailWord_400107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400107).length < 2 ^ (prefixWord ++ tailWord_400107).sum := by decide
  have hdescent : baseEnd_400107 < baseStart_400107 := by decide
  rcases family_descends (prefixWord ++ tailWord_400107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400124 : List Nat := [2, 2, 2, 1, 3, 2, 1, 3, 7]
def baseStart_400124 : Nat := 118140960795 + 400124 * 2 ^ 59
def prefixEnd_400124 : Nat := 4983230072969 + 3 ^ 40 * 400124 * 2
def baseEnd_400124 : Nat := 22828437044410860745541

theorem tailTrace_400124 : CollatzResearch.WordTrace tailWord_400124 prefixEnd_400124 22828437044410860745541 := by
  unfold tailWord_400124
  simp only [CollatzResearch.WordTrace]
  refine ⟨7296860601213279291911713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9729147468284372389215617 7296860601213279291911713)
  ·
    refine ⟨5472645450909959468933785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7296860601213279291911713 5472645450909959468933785)
    ·
      refine ⟨4104484088182469601700339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5472645450909959468933785 4104484088182469601700339)
      ·
        refine ⟨6156726132273704402550509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4104484088182469601700339 6156726132273704402550509)
        ·
          refine ⟨2308772299602639150956441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6156726132273704402550509 2308772299602639150956441)
          ·
            refine ⟨1731579224701979363217331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2308772299602639150956441 1731579224701979363217331)
            ·
              refine ⟨2597368837052969044825997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1731579224701979363217331 2597368837052969044825997)
              ·
                refine ⟨974013313894863391809749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2597368837052969044825997 974013313894863391809749)
                ·
                  refine ⟨22828437044410860745541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 974013313894863391809749 22828437044410860745541)
                  ·
                    rfl

theorem cell23_400124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 7].length) (baseStart_400124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400124 prefixEnd_400124 := by exact prefixLift 400124
  have htrace : WordTrace (prefixWord ++ tailWord_400124) baseStart_400124 baseEnd_400124 := by
    simpa [prefixWord, tailWord_400124, baseEnd_400124] using wordTrace_append hprefix tailTrace_400124
  have hstable : (prefixWord ++ tailWord_400124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400124).length < 2 ^ (prefixWord ++ tailWord_400124).sum := by decide
  have hdescent : baseEnd_400124 < baseStart_400124 := by decide
  rcases family_descends (prefixWord ++ tailWord_400124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400135 : List Nat := [1, 1, 4, 4, 1, 3, 1, 1, 1, 4, 2]
def baseStart_400135 : Nat := 118140960795 + 400135 * 2 ^ 59
def prefixEnd_400135 : Nat := 4983230072969 + 3 ^ 40 * 400135 * 2
def baseEnd_400135 : Nat := 205461581686897203672319

theorem tailTrace_400135 : CollatzResearch.WordTrace tailWord_400135 prefixEnd_400135 205461581686897203672319 := by
  unfold tailWord_400135
  simp only [CollatzResearch.WordTrace]
  refine ⟨14594122405386707462473859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9729414936924471641649239 14594122405386707462473859)
  ·
    refine ⟨21891183608080061193710789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14594122405386707462473859 21891183608080061193710789)
    ·
      refine ⟨4104596926515011473820773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21891183608080061193710789 4104596926515011473820773)
      ·
        refine ⟨769611923721564651341395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4104596926515011473820773 769611923721564651341395)
        ·
          refine ⟨1154417885582346977012093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 769611923721564651341395 1154417885582346977012093)
          ·
            refine ⟨432906707093380116379535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1154417885582346977012093 432906707093380116379535)
            ·
              refine ⟨649360060640070174569303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432906707093380116379535 649360060640070174569303)
              ·
                refine ⟨974040090960105261853955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 649360060640070174569303 974040090960105261853955)
                ·
                  refine ⟨1461060136440157892780933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 974040090960105261853955 1461060136440157892780933)
                  ·
                    refine ⟨273948775582529604896425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1461060136440157892780933 273948775582529604896425)
                    ·
                      refine ⟨205461581686897203672319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 273948775582529604896425 205461581686897203672319)
                      ·
                        rfl

theorem cell23_400135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_400135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400135 prefixEnd_400135 := by exact prefixLift 400135
  have htrace : WordTrace (prefixWord ++ tailWord_400135) baseStart_400135 baseEnd_400135 := by
    simpa [prefixWord, tailWord_400135, baseEnd_400135] using wordTrace_append hprefix tailTrace_400135
  have hstable : (prefixWord ++ tailWord_400135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400135).length < 2 ^ (prefixWord ++ tailWord_400135).sum := by decide
  have hdescent : baseEnd_400135 < baseStart_400135 := by decide
  rcases family_descends (prefixWord ++ tailWord_400135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400154 : List Nat := [3, 1, 1, 3, 2, 1, 1, 3, 1, 7]
def baseStart_400154 : Nat := 118140960795 + 400154 * 2 ^ 59
def prefixEnd_400154 : Nat := 4983230072969 + 3 ^ 40 * 400154 * 2
def baseEnd_400154 : Nat := 68490445939777543111577

theorem tailTrace_400154 : CollatzResearch.WordTrace tailWord_400154 prefixEnd_400154 68490445939777543111577 := by
  unfold tailWord_400154
  simp only [CollatzResearch.WordTrace]
  refine ⟨3648703848079468426853879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9729876928211915804943677 3648703848079468426853879)
  ·
    refine ⟨5473055772119202640280819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3648703848079468426853879 5473055772119202640280819)
    ·
      refine ⟨8209583658178803960421229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5473055772119202640280819 8209583658178803960421229)
      ·
        refine ⟨3078593871817051485157961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8209583658178803960421229 3078593871817051485157961)
        ·
          refine ⟨2308945403862788613868471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3078593871817051485157961 2308945403862788613868471)
          ·
            refine ⟨3463418105794182920802707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2308945403862788613868471 3463418105794182920802707)
            ·
              refine ⟨5195127158691274381204061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3463418105794182920802707 5195127158691274381204061)
              ·
                refine ⟨1948172684509227892951523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5195127158691274381204061 1948172684509227892951523)
                ·
                  refine ⟨2922259026763841839427285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1948172684509227892951523 2922259026763841839427285)
                  ·
                    refine ⟨68490445939777543111577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2922259026763841839427285 68490445939777543111577)
                    ·
                      rfl

theorem cell23_400154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 1, 7].length) (baseStart_400154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400154 prefixEnd_400154 := by exact prefixLift 400154
  have htrace : WordTrace (prefixWord ++ tailWord_400154) baseStart_400154 baseEnd_400154 := by
    simpa [prefixWord, tailWord_400154, baseEnd_400154] using wordTrace_append hprefix tailTrace_400154
  have hstable : (prefixWord ++ tailWord_400154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400154).length < 2 ^ (prefixWord ++ tailWord_400154).sum := by decide
  have hdescent : baseEnd_400154 < baseStart_400154 := by decide
  rcases family_descends (prefixWord ++ tailWord_400154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400181 : List Nat := [1, 3, 3, 1, 3, 2, 1, 1, 1, 2, 5]
def baseStart_400181 : Nat := 118140960795 + 400181 * 2 ^ 59
def prefixEnd_400181 : Nat := 4983230072969 + 3 ^ 40 * 400181 * 2
def baseEnd_400181 : Nat := 205485201797004023697107

theorem tailTrace_400181 : CollatzResearch.WordTrace tailWord_400181 prefixEnd_400181 205485201797004023697107 := by
  unfold tailWord_400181
  simp only [CollatzResearch.WordTrace]
  refine ⟨14595800163220057318648397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9730533442146704879098931 14595800163220057318648397)
  ·
    refine ⟨5473425061207521494493149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14595800163220057318648397 5473425061207521494493149)
    ·
      refine ⟨2052534397952820560434931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5473425061207521494493149 2052534397952820560434931)
      ·
        refine ⟨3078801596929230840652397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2052534397952820560434931 3078801596929230840652397)
        ·
          refine ⟨1154550598848461565244649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3078801596929230840652397 1154550598848461565244649)
          ·
            refine ⟨865912949136346173933487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1154550598848461565244649 865912949136346173933487)
            ·
              refine ⟨1298869423704519260900231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 865912949136346173933487 1298869423704519260900231)
              ·
                refine ⟨1948304135556778891350347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1298869423704519260900231 1948304135556778891350347)
                ·
                  refine ⟨2922456203335168337025521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1948304135556778891350347 2922456203335168337025521)
                  ·
                    refine ⟨2191842152501376252769141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2922456203335168337025521 2191842152501376252769141)
                    ·
                      refine ⟨205485201797004023697107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2191842152501376252769141 205485201797004023697107)
                      ·
                        rfl

theorem cell23_400181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_400181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400181 prefixEnd_400181 := by exact prefixLift 400181
  have htrace : WordTrace (prefixWord ++ tailWord_400181) baseStart_400181 baseEnd_400181 := by
    simpa [prefixWord, tailWord_400181, baseEnd_400181] using wordTrace_append hprefix tailTrace_400181
  have hstable : (prefixWord ++ tailWord_400181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400181).length < 2 ^ (prefixWord ++ tailWord_400181).sum := by decide
  have hdescent : baseEnd_400181 < baseStart_400181 := by decide
  rcases family_descends (prefixWord ++ tailWord_400181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400205 : List Nat := [1, 6, 1, 2, 2, 1, 2, 1, 2, 5]
def baseStart_400205 : Nat := 118140960795 + 400205 * 2 ^ 59
def prefixEnd_400205 : Nat := 4983230072969 + 3 ^ 40 * 400205 * 2
def baseEnd_400205 : Nat := 68499175110903976598999

theorem tailTrace_400205 : CollatzResearch.WordTrace tailWord_400205 prefixEnd_400205 68499175110903976598999 := by
  unfold tailWord_400205
  simp only [CollatzResearch.WordTrace]
  refine ⟨14596675515133109417522069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9731117010088739611681379 14596675515133109417522069)
  ·
    refine ⟨684219164771864503946347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14596675515133109417522069 684219164771864503946347)
    ·
      refine ⟨1026328747157796755919521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 684219164771864503946347 1026328747157796755919521)
      ·
        refine ⟨769746560368347566939641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1026328747157796755919521 769746560368347566939641)
        ·
          refine ⟨577309920276260675204731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 769746560368347566939641 577309920276260675204731)
          ·
            refine ⟨865964880414391012807097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 577309920276260675204731 865964880414391012807097)
            ·
              refine ⟨649473660310793259605323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 865964880414391012807097 649473660310793259605323)
              ·
                refine ⟨974210490466189889407985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 649473660310793259605323 974210490466189889407985)
                ·
                  refine ⟨730657867849642417055989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 974210490466189889407985 730657867849642417055989)
                  ·
                    refine ⟨68499175110903976598999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 730657867849642417055989 68499175110903976598999)
                    ·
                      rfl

theorem cell23_400205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_400205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400205 prefixEnd_400205 := by exact prefixLift 400205
  have htrace : WordTrace (prefixWord ++ tailWord_400205) baseStart_400205 baseEnd_400205 := by
    simpa [prefixWord, tailWord_400205, baseEnd_400205] using wordTrace_append hprefix tailTrace_400205
  have hstable : (prefixWord ++ tailWord_400205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400205).length < 2 ^ (prefixWord ++ tailWord_400205).sum := by decide
  have hdescent : baseEnd_400205 < baseStart_400205 := by decide
  rcases family_descends (prefixWord ++ tailWord_400205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400228 : List Nat := [2, 3, 1, 1, 4, 1, 2, 2, 2, 2, 3]
def baseStart_400228 : Nat := 118140960795 + 400228 * 2 ^ 59
def prefixEnd_400228 : Nat := 4983230072969 + 3 ^ 40 * 400228 * 2
def baseEnd_400228 : Nat := 205509335387765339809391

theorem tailTrace_400228 : CollatzResearch.WordTrace tailWord_400228 prefixEnd_400228 205509335387765339809391 := by
  unfold tailWord_400228
  simp only [CollatzResearch.WordTrace]
  refine ⟨7298757197024892172804669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9731676262699856230406225 7298757197024892172804669)
  ·
    refine ⟨2737033948884334564801751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7298757197024892172804669 2737033948884334564801751)
    ·
      refine ⟨4105550923326501847202627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2737033948884334564801751 4105550923326501847202627)
      ·
        refine ⟨6158326384989752770803941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4105550923326501847202627 6158326384989752770803941)
        ·
          refine ⟨1154686197185578644525739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6158326384989752770803941 1154686197185578644525739)
          ·
            refine ⟨1732029295778367966788609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1154686197185578644525739 1732029295778367966788609)
            ·
              refine ⟨1299021971833775975091457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1732029295778367966788609 1299021971833775975091457)
              ·
                refine ⟨974266478875331981318593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1299021971833775975091457 974266478875331981318593)
                ·
                  refine ⟨730699859156498985988945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 974266478875331981318593 730699859156498985988945)
                  ·
                    refine ⟨548024894367374239491709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 730699859156498985988945 548024894367374239491709)
                    ·
                      refine ⟨205509335387765339809391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 548024894367374239491709 205509335387765339809391)
                      ·
                        rfl

theorem cell23_400228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 2, 2, 3].length) (baseStart_400228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400228 prefixEnd_400228 := by exact prefixLift 400228
  have htrace : WordTrace (prefixWord ++ tailWord_400228) baseStart_400228 baseEnd_400228 := by
    simpa [prefixWord, tailWord_400228, baseEnd_400228] using wordTrace_append hprefix tailTrace_400228
  have hstable : (prefixWord ++ tailWord_400228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400228).length < 2 ^ (prefixWord ++ tailWord_400228).sum := by decide
  have hdescent : baseEnd_400228 < baseStart_400228 := by decide
  rcases family_descends (prefixWord ++ tailWord_400228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400231 : List Nat := [1, 1, 5, 1, 2, 2, 1, 4, 6]
def baseStart_400231 : Nat := 118140960795 + 400231 * 2 ^ 59
def prefixEnd_400231 : Nat := 4983230072969 + 3 ^ 40 * 400231 * 2
def baseEnd_400231 : Nat := 22834541758858758674653

theorem tailTrace_400231 : CollatzResearch.WordTrace tailWord_400231 prefixEnd_400231 22834541758858758674653 := by
  unfold tailWord_400231
  simp only [CollatzResearch.WordTrace]
  refine ⟨14597623813038915857968547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9731749208692610571979031 14597623813038915857968547)
  ·
    refine ⟨21896435719558373786952821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14597623813038915857968547 21896435719558373786952821)
    ·
      refine ⟨2052790848708597542526827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21896435719558373786952821 2052790848708597542526827)
      ·
        refine ⟨3079186273062896313790241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2052790848708597542526827 3079186273062896313790241)
        ·
          refine ⟨2309389704797172235342681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3079186273062896313790241 2309389704797172235342681)
          ·
            refine ⟨1732042278597879176507011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2309389704797172235342681 1732042278597879176507011)
            ·
              refine ⟨2598063417896818764760517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1732042278597879176507011 2598063417896818764760517)
              ·
                refine ⟨487136890855653518392597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2598063417896818764760517 487136890855653518392597)
                ·
                  refine ⟨22834541758858758674653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 487136890855653518392597 22834541758858758674653)
                  ·
                    rfl

theorem cell23_400231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4, 6].length) (baseStart_400231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400231 prefixEnd_400231 := by exact prefixLift 400231
  have htrace : WordTrace (prefixWord ++ tailWord_400231) baseStart_400231 baseEnd_400231 := by
    simpa [prefixWord, tailWord_400231, baseEnd_400231] using wordTrace_append hprefix tailTrace_400231
  have hstable : (prefixWord ++ tailWord_400231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400231).length < 2 ^ (prefixWord ++ tailWord_400231).sum := by decide
  have hdescent : baseEnd_400231 < baseStart_400231 := by decide
  rcases family_descends (prefixWord ++ tailWord_400231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400235 : List Nat := [1, 1, 1, 1, 2, 2, 8, 2, 1, 4]
def baseStart_400235 : Nat := 118140960795 + 400235 * 2 ^ 59
def prefixEnd_400235 : Nat := 4983230072969 + 3 ^ 40 * 400235 * 2
def baseEnd_400235 : Nat := 68504309917448937473953

theorem tailTrace_400235 : CollatzResearch.WordTrace tailWord_400235 prefixEnd_400235 68504309917448937473953 := by
  unfold tailWord_400235
  simp only [CollatzResearch.WordTrace]
  refine ⟨14597769705024424541114159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9731846470016283027409439 14597769705024424541114159)
  ·
    refine ⟨21896654557536636811671239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14597769705024424541114159 21896654557536636811671239)
    ·
      refine ⟨32844981836304955217506859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21896654557536636811671239 32844981836304955217506859)
      ·
        refine ⟨49267472754457432826260289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32844981836304955217506859 49267472754457432826260289)
        ·
          refine ⟨36950604565843074619695217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49267472754457432826260289 36950604565843074619695217)
          ·
            refine ⟨27712953424382305964771413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36950604565843074619695217 27712953424382305964771413)
            ·
              refine ⟨324761172941980148024665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 27712953424382305964771413 324761172941980148024665)
              ·
                refine ⟨243570879706485111018499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 324761172941980148024665 243570879706485111018499)
                ·
                  refine ⟨365356319559727666527749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 243570879706485111018499 365356319559727666527749)
                  ·
                    refine ⟨68504309917448937473953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 365356319559727666527749 68504309917448937473953)
                    ·
                      rfl

theorem cell23_400235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 2, 1, 4].length) (baseStart_400235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400235 prefixEnd_400235 := by exact prefixLift 400235
  have htrace : WordTrace (prefixWord ++ tailWord_400235) baseStart_400235 baseEnd_400235 := by
    simpa [prefixWord, tailWord_400235, baseEnd_400235] using wordTrace_append hprefix tailTrace_400235
  have hstable : (prefixWord ++ tailWord_400235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400235).length < 2 ^ (prefixWord ++ tailWord_400235).sum := by decide
  have hdescent : baseEnd_400235 < baseStart_400235 := by decide
  rcases family_descends (prefixWord ++ tailWord_400235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400261 : List Nat := [1, 3, 1, 1, 3, 3, 2, 1, 3, 5]
def baseStart_400261 : Nat := 118140960795 + 400261 * 2 ^ 59
def prefixEnd_400261 : Nat := 4983230072969 + 3 ^ 40 * 400261 * 2
def baseEnd_400261 : Nat := 68508760083121236898913

theorem tailTrace_400261 : CollatzResearch.WordTrace tailWord_400261 prefixEnd_400261 68508760083121236898913 := by
  unfold tailWord_400261
  simp only [CollatzResearch.WordTrace]
  refine ⟨14598718002930230981560637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9732478668620153987707091 14598718002930230981560637)
  ·
    refine ⟨5474519251098836618085239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14598718002930230981560637 5474519251098836618085239)
    ·
      refine ⟨8211778876648254927127859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5474519251098836618085239 8211778876648254927127859)
      ·
        refine ⟨12317668314972382390691789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8211778876648254927127859 12317668314972382390691789)
        ·
          refine ⟨4619125618114643396509421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12317668314972382390691789 4619125618114643396509421)
          ·
            refine ⟨1732172106792991273691033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4619125618114643396509421 1732172106792991273691033)
            ·
              refine ⟨1299129080094743455268275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1732172106792991273691033 1299129080094743455268275)
              ·
                refine ⟨1948693620142115182902413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1299129080094743455268275 1948693620142115182902413)
                ·
                  refine ⟨730760107553293193588405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1948693620142115182902413 730760107553293193588405)
                  ·
                    refine ⟨68508760083121236898913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 730760107553293193588405 68508760083121236898913)
                    ·
                      rfl

theorem cell23_400261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3, 5].length) (baseStart_400261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400261 prefixEnd_400261 := by exact prefixLift 400261
  have htrace : WordTrace (prefixWord ++ tailWord_400261) baseStart_400261 baseEnd_400261 := by
    simpa [prefixWord, tailWord_400261, baseEnd_400261] using wordTrace_append hprefix tailTrace_400261
  have hstable : (prefixWord ++ tailWord_400261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400261).length < 2 ^ (prefixWord ++ tailWord_400261).sum := by decide
  have hdescent : baseEnd_400261 < baseStart_400261 := by decide
  rcases family_descends (prefixWord ++ tailWord_400261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400338 : List Nat := [3, 2, 2, 3, 1, 3, 9]
def baseStart_400338 : Nat := 118140960795 + 400338 * 2 ^ 59
def prefixEnd_400338 : Nat := 4983230072969 + 3 ^ 40 * 400338 * 2
def baseEnd_400338 : Nat := 2537849608145184067085

theorem tailTrace_400338 : CollatzResearch.WordTrace tailWord_400338 prefixEnd_400338 2537849608145184067085 := by
  unfold tailWord_400338
  simp only [CollatzResearch.WordTrace]
  refine ⟨3650381605912818283028417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9734350949100848754742445 3650381605912818283028417)
  ·
    refine ⟨2737786204434613712271313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3650381605912818283028417 2737786204434613712271313)
    ·
      refine ⟨2053339653325960284203485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2737786204434613712271313 2053339653325960284203485)
      ·
        refine ⟨770002369997235106576307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2053339653325960284203485 770002369997235106576307)
        ·
          refine ⟨1155003554995852659864461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 770002369997235106576307 1155003554995852659864461)
          ·
            refine ⟨433126333123444747449173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1155003554995852659864461 433126333123444747449173)
            ·
              refine ⟨2537849608145184067085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 433126333123444747449173 2537849608145184067085)
              ·
                rfl

theorem cell23_400338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 9].length) (baseStart_400338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400338 prefixEnd_400338 := by exact prefixLift 400338
  have htrace : WordTrace (prefixWord ++ tailWord_400338) baseStart_400338 baseEnd_400338 := by
    simpa [prefixWord, tailWord_400338, baseEnd_400338] using wordTrace_append hprefix tailTrace_400338
  have hstable : (prefixWord ++ tailWord_400338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400338).length < 2 ^ (prefixWord ++ tailWord_400338).sum := by decide
  have hdescent : baseEnd_400338 < baseStart_400338 := by decide
  rcases family_descends (prefixWord ++ tailWord_400338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400349 : List Nat := [1, 4, 3, 1, 2, 3, 1, 1, 3, 2, 2]
def baseStart_400349 : Nat := 118140960795 + 400349 * 2 ^ 59
def prefixEnd_400349 : Nat := 4983230072969 + 3 ^ 40 * 400349 * 2
def baseEnd_400349 : Nat := 205571466546959366396335

theorem tailTrace_400349 : CollatzResearch.WordTrace tailWord_400349 prefixEnd_400349 205571466546959366396335 := by
  unfold tailWord_400349
  simp only [CollatzResearch.WordTrace]
  refine ⟨14601927626611422010764101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9734618417740948007176067 14601927626611422010764101)
  ·
    refine ⟨2737861429989641627018269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14601927626611422010764101 2737861429989641627018269)
    ·
      refine ⟨1026698036246115610131851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2737861429989641627018269 1026698036246115610131851)
      ·
        refine ⟨1540047054369173415197777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1026698036246115610131851 1540047054369173415197777)
        ·
          refine ⟨1155035290776880061398333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1540047054369173415197777 1155035290776880061398333)
          ·
            refine ⟨433138234041330023024375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1155035290776880061398333 433138234041330023024375)
            ·
              refine ⟨649707351061995034536563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433138234041330023024375 649707351061995034536563)
              ·
                refine ⟨974561026592992551804845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 649707351061995034536563 974561026592992551804845)
                ·
                  refine ⟨365460384972372206926817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 974561026592992551804845 365460384972372206926817)
                  ·
                    refine ⟨274095288729279155195113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 365460384972372206926817 274095288729279155195113)
                    ·
                      refine ⟨205571466546959366396335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 274095288729279155195113 205571466546959366396335)
                      ·
                        rfl

theorem cell23_400349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_400349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400349 prefixEnd_400349 := by exact prefixLift 400349
  have htrace : WordTrace (prefixWord ++ tailWord_400349) baseStart_400349 baseEnd_400349 := by
    simpa [prefixWord, tailWord_400349, baseEnd_400349] using wordTrace_append hprefix tailTrace_400349
  have hstable : (prefixWord ++ tailWord_400349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400349).length < 2 ^ (prefixWord ++ tailWord_400349).sum := by decide
  have hdescent : baseEnd_400349 < baseStart_400349 := by decide
  rcases family_descends (prefixWord ++ tailWord_400349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400381 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 4, 6]
def baseStart_400381 : Nat := 118140960795 + 400381 * 2 ^ 59
def prefixEnd_400381 : Nat := 4983230072969 + 3 ^ 40 * 400381 * 2
def baseEnd_400381 : Nat := 68529299309301080398729

theorem tailTrace_400381 : CollatzResearch.WordTrace tailWord_400381 prefixEnd_400381 68529299309301080398729 := by
  unfold tailWord_400381
  simp only [CollatzResearch.WordTrace]
  refine ⟨14603094762495491475928997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9735396508330327650619331 14603094762495491475928997)
  ·
    refine ⟨2738080267967904651736687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14603094762495491475928997 2738080267967904651736687)
    ·
      refine ⟨4107120401951856977605031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2738080267967904651736687 4107120401951856977605031)
      ·
        refine ⟨6160680602927785466407547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4107120401951856977605031 6160680602927785466407547)
        ·
          refine ⟨9241020904391678199611321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6160680602927785466407547 9241020904391678199611321)
          ·
            refine ⟨6930765678293758649708491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9241020904391678199611321 6930765678293758649708491)
            ·
              refine ⟨10396148517440637974562737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6930765678293758649708491 10396148517440637974562737)
              ·
                refine ⟨7797111388080478480922053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10396148517440637974562737 7797111388080478480922053)
                ·
                  refine ⟨1461958385265089715172885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7797111388080478480922053 1461958385265089715172885)
                  ·
                    refine ⟨68529299309301080398729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1461958385265089715172885 68529299309301080398729)
                    ·
                      rfl

theorem cell23_400381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_400381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400381 prefixEnd_400381 := by exact prefixLift 400381
  have htrace : WordTrace (prefixWord ++ tailWord_400381) baseStart_400381 baseEnd_400381 := by
    simpa [prefixWord, tailWord_400381, baseEnd_400381] using wordTrace_append hprefix tailTrace_400381
  have hstable : (prefixWord ++ tailWord_400381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400381).length < 2 ^ (prefixWord ++ tailWord_400381).sum := by decide
  have hdescent : baseEnd_400381 < baseStart_400381 := by decide
  rcases family_descends (prefixWord ++ tailWord_400381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400382 : List Nat := [4, 2, 2, 2, 2, 1, 1, 2, 1, 3, 3]
def baseStart_400382 : Nat := 118140960795 + 400382 * 2 ^ 59
def prefixEnd_400382 : Nat := 4983230072969 + 3 ^ 40 * 400382 * 2
def baseEnd_400382 : Nat := 205588411408557737283683

theorem tailTrace_400382 : CollatzResearch.WordTrace tailWord_400382 prefixEnd_400382 205588411408557737283683 := by
  unfold tailWord_400382
  simp only [CollatzResearch.WordTrace]
  refine ⟨1825391404436483580839425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9735420823661245764476933 1825391404436483580839425)
  ·
    refine ⟨1369043553327362685629569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1825391404436483580839425 1369043553327362685629569)
    ·
      refine ⟨1026782664995522014222177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1369043553327362685629569 1026782664995522014222177)
      ·
        refine ⟨770086998746641510666633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1026782664995522014222177 770086998746641510666633)
        ·
          refine ⟨577565249059981132999975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 770086998746641510666633 577565249059981132999975)
          ·
            refine ⟨866347873589971699499963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 577565249059981132999975 866347873589971699499963)
            ·
              refine ⟨1299521810384957549249945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 866347873589971699499963 1299521810384957549249945)
              ·
                refine ⟨974641357788718161937459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1299521810384957549249945 974641357788718161937459)
                ·
                  refine ⟨1461962036683077242906189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 974641357788718161937459 1461962036683077242906189)
                  ·
                    refine ⟨548235763756153966089821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1461962036683077242906189 548235763756153966089821)
                    ·
                      refine ⟨205588411408557737283683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 548235763756153966089821 205588411408557737283683)
                      ·
                        rfl

theorem cell23_400382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_400382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400382 prefixEnd_400382 := by exact prefixLift 400382
  have htrace : WordTrace (prefixWord ++ tailWord_400382) baseStart_400382 baseEnd_400382 := by
    simpa [prefixWord, tailWord_400382, baseEnd_400382] using wordTrace_append hprefix tailTrace_400382
  have hstable : (prefixWord ++ tailWord_400382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400382).length < 2 ^ (prefixWord ++ tailWord_400382).sum := by decide
  have hdescent : baseEnd_400382 < baseStart_400382 := by decide
  rcases family_descends (prefixWord ++ tailWord_400382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400386 : List Nat := [3, 4, 1, 3, 1, 1, 3, 1, 1, 2, 3]
def baseStart_400386 : Nat := 118140960795 + 400386 * 2 ^ 59
def prefixEnd_400386 : Nat := 4983230072969 + 3 ^ 40 * 400386 * 2
def baseEnd_400386 : Nat := 205590465331175721633665

theorem tailTrace_400386 : CollatzResearch.WordTrace tailWord_400386 prefixEnd_400386 205590465331175721633665 := by
  unfold tailWord_400386
  simp only [CollatzResearch.WordTrace]
  refine ⟨3650819281869344332465253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9735518084984918219907341 3650819281869344332465253)
  ·
    refine ⟨684528615350502062337235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3650819281869344332465253 684528615350502062337235)
    ·
      refine ⟨1026792923025753093505853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 684528615350502062337235 1026792923025753093505853)
      ·
        refine ⟨385047346134657410064695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1026792923025753093505853 385047346134657410064695)
        ·
          refine ⟨577571019201986115097043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385047346134657410064695 577571019201986115097043)
          ·
            refine ⟨866356528802979172645565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 577571019201986115097043 866356528802979172645565)
            ·
              refine ⟨324883698301117189742087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 866356528802979172645565 324883698301117189742087)
              ·
                refine ⟨487325547451675784613131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 324883698301117189742087 487325547451675784613131)
                ·
                  refine ⟨730988321177513676919697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 487325547451675784613131 730988321177513676919697)
                  ·
                    refine ⟨548241240883135257689773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 730988321177513676919697 548241240883135257689773)
                    ·
                      refine ⟨205590465331175721633665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 548241240883135257689773 205590465331175721633665)
                      ·
                        rfl

theorem cell23_400386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_400386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400386 prefixEnd_400386 := by exact prefixLift 400386
  have htrace : WordTrace (prefixWord ++ tailWord_400386) baseStart_400386 baseEnd_400386 := by
    simpa [prefixWord, tailWord_400386, baseEnd_400386] using wordTrace_append hprefix tailTrace_400386
  have hstable : (prefixWord ++ tailWord_400386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400386).length < 2 ^ (prefixWord ++ tailWord_400386).sum := by decide
  have hdescent : baseEnd_400386 < baseStart_400386 := by decide
  rcases family_descends (prefixWord ++ tailWord_400386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400401 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 4]
def baseStart_400401 : Nat := 118140960795 + 400401 * 2 ^ 59
def prefixEnd_400401 : Nat := 4983230072969 + 3 ^ 40 * 400401 * 2
def baseEnd_400401 : Nat := 205598167540993162946095

theorem tailTrace_400401 : CollatzResearch.WordTrace tailWord_400401 prefixEnd_400401 205598167540993162946095 := by
  unfold tailWord_400401
  simp only [CollatzResearch.WordTrace]
  refine ⟨14603824222423034891657057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9735882814948689927771371 14603824222423034891657057)
  ·
    refine ⟨10952868166817276168742793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14603824222423034891657057 10952868166817276168742793)
    ·
      refine ⟨8214651125112957126557095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10952868166817276168742793 8214651125112957126557095)
      ·
        refine ⟨12321976687669435689835643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8214651125112957126557095 12321976687669435689835643)
        ·
          refine ⟨18482965031504153534753465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12321976687669435689835643 18482965031504153534753465)
          ·
            refine ⟨13862223773628115151065099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18482965031504153534753465 13862223773628115151065099)
            ·
              refine ⟨20793335660442172726597649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13862223773628115151065099 20793335660442172726597649)
              ·
                refine ⟨15595001745331629544948237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20793335660442172726597649 15595001745331629544948237)
                ·
                  refine ⟨5848125654499361079355589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15595001745331629544948237 5848125654499361079355589)
                  ·
                    refine ⟨1096523560218630202379173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5848125654499361079355589 1096523560218630202379173)
                    ·
                      refine ⟨205598167540993162946095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1096523560218630202379173 205598167540993162946095)
                      ·
                        rfl

theorem cell23_400401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 4].length) (baseStart_400401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400401 prefixEnd_400401 := by exact prefixLift 400401
  have htrace : WordTrace (prefixWord ++ tailWord_400401) baseStart_400401 baseEnd_400401 := by
    simpa [prefixWord, tailWord_400401, baseEnd_400401] using wordTrace_append hprefix tailTrace_400401
  have hstable : (prefixWord ++ tailWord_400401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400401).length < 2 ^ (prefixWord ++ tailWord_400401).sum := by decide
  have hdescent : baseEnd_400401 < baseStart_400401 := by decide
  rcases family_descends (prefixWord ++ tailWord_400401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400408 : List Nat := [2, 1, 2, 3, 2, 2, 1, 1, 2, 4, 3]
def baseStart_400408 : Nat := 118140960795 + 400408 * 2 ^ 59
def prefixEnd_400408 : Nat := 4983230072969 + 3 ^ 40 * 400408 * 2
def baseEnd_400408 : Nat := 205601761905574635558563

theorem tailTrace_400408 : CollatzResearch.WordTrace tailWord_400408 prefixEnd_400408 205601761905574635558563 := by
  unfold tailWord_400408
  simp only [CollatzResearch.WordTrace]
  refine ⟨7302039766698837543580939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9736053022265116724774585 7302039766698837543580939)
  ·
    refine ⟨10953059650048256315371409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7302039766698837543580939 10953059650048256315371409)
    ·
      refine ⟨8214794737536192236528557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10953059650048256315371409 8214794737536192236528557)
      ·
        refine ⟨3080548026576072088698209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8214794737536192236528557 3080548026576072088698209)
        ·
          refine ⟨2310411019932054066523657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3080548026576072088698209 2310411019932054066523657)
          ·
            refine ⟨1732808264949040549892743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2310411019932054066523657 1732808264949040549892743)
            ·
              refine ⟨2599212397423560824839115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1732808264949040549892743 2599212397423560824839115)
              ·
                refine ⟨3898818596135341237258673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2599212397423560824839115 3898818596135341237258673)
                ·
                  refine ⟨2924113947101505927944005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3898818596135341237258673 2924113947101505927944005)
                  ·
                    refine ⟨548271365081532361489501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2924113947101505927944005 548271365081532361489501)
                    ·
                      refine ⟨205601761905574635558563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 548271365081532361489501 205601761905574635558563)
                      ·
                        rfl

theorem cell23_400408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_400408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400408 prefixEnd_400408 := by exact prefixLift 400408
  have htrace : WordTrace (prefixWord ++ tailWord_400408) baseStart_400408 baseEnd_400408 := by
    simpa [prefixWord, tailWord_400408, baseEnd_400408] using wordTrace_append hprefix tailTrace_400408
  have hstable : (prefixWord ++ tailWord_400408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400408).length < 2 ^ (prefixWord ++ tailWord_400408).sum := by decide
  have hdescent : baseEnd_400408 < baseStart_400408 := by decide
  rcases family_descends (prefixWord ++ tailWord_400408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400418 : List Nat := [3, 3, 1, 1, 1, 3, 1, 1, 1, 4, 4]
def baseStart_400418 : Nat := 118140960795 + 400418 * 2 ^ 59
def prefixEnd_400418 : Nat := 4983230072969 + 3 ^ 40 * 400418 * 2
def baseEnd_400418 : Nat := 205606896712119596433517

theorem tailTrace_400418 : CollatzResearch.WordTrace tailWord_400418 prefixEnd_400418 205606896712119596433517 := by
  unfold tailWord_400418
  simp only [CollatzResearch.WordTrace]
  refine ⟨3651111065840361698756477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9736296175574297863350605 3651111065840361698756477)
  ·
    refine ⟨1369166649690135637033679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3651111065840361698756477 1369166649690135637033679)
    ·
      refine ⟨2053749974535203455550519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1369166649690135637033679 2053749974535203455550519)
      ·
        refine ⟨3080624961802805183325779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2053749974535203455550519 3080624961802805183325779)
        ·
          refine ⟨4620937442704207774988669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3080624961802805183325779 4620937442704207774988669)
          ·
            refine ⟨1732851541014077915620751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4620937442704207774988669 1732851541014077915620751)
            ·
              refine ⟨2599277311521116873431127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1732851541014077915620751 2599277311521116873431127)
              ·
                refine ⟨3898915967281675310146691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2599277311521116873431127 3898915967281675310146691)
                ·
                  refine ⟨5848373950922512965220037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3898915967281675310146691 5848373950922512965220037)
                  ·
                    refine ⟨1096570115797971180978757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5848373950922512965220037 1096570115797971180978757)
                    ·
                      refine ⟨205606896712119596433517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1096570115797971180978757 205606896712119596433517)
                      ·
                        rfl

theorem cell23_400418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_400418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400418 prefixEnd_400418 := by exact prefixLift 400418
  have htrace : WordTrace (prefixWord ++ tailWord_400418) baseStart_400418 baseEnd_400418 := by
    simpa [prefixWord, tailWord_400418, baseEnd_400418] using wordTrace_append hprefix tailTrace_400418
  have hstable : (prefixWord ++ tailWord_400418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400418).length < 2 ^ (prefixWord ++ tailWord_400418).sum := by decide
  have hdescent : baseEnd_400418 < baseStart_400418 := by decide
  rcases family_descends (prefixWord ++ tailWord_400418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400445 : List Nat := [1, 4, 1, 3, 1, 2, 1, 5, 5]
def baseStart_400445 : Nat := 118140960795 + 400445 * 2 ^ 59
def prefixEnd_400445 : Nat := 4983230072969 + 3 ^ 40 * 400445 * 2
def baseEnd_400445 : Nat := 22846751187754554532877

theorem tailTrace_400445 : CollatzResearch.WordTrace tailWord_400445 prefixEnd_400445 22846751187754554532877 := by
  unfold tailWord_400445
  simp only [CollatzResearch.WordTrace]
  refine ⟨14605429034263630406258789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9736952689509086937505859 14605429034263630406258789)
  ·
    refine ⟨2738517943924430701173523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14605429034263630406258789 2738517943924430701173523)
    ·
      refine ⟨4107776915886646051760285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2738517943924430701173523 4107776915886646051760285)
      ·
        refine ⟨1540416343457492269410107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4107776915886646051760285 1540416343457492269410107)
        ·
          refine ⟨2310624515186238404115161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1540416343457492269410107 2310624515186238404115161)
          ·
            refine ⟨1732968386389678803086371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2310624515186238404115161 1732968386389678803086371)
            ·
              refine ⟨2599452579584518204629557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1732968386389678803086371 2599452579584518204629557)
              ·
                refine ⟨243698679336048581684021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2599452579584518204629557 243698679336048581684021)
                ·
                  refine ⟨22846751187754554532877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 243698679336048581684021 22846751187754554532877)
                  ·
                    rfl

theorem cell23_400445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 5, 5].length) (baseStart_400445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400445 prefixEnd_400445 := by exact prefixLift 400445
  have htrace : WordTrace (prefixWord ++ tailWord_400445) baseStart_400445 baseEnd_400445 := by
    simpa [prefixWord, tailWord_400445, baseEnd_400445] using wordTrace_append hprefix tailTrace_400445
  have hstable : (prefixWord ++ tailWord_400445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400445).length < 2 ^ (prefixWord ++ tailWord_400445).sum := by decide
  have hdescent : baseEnd_400445 < baseStart_400445 := by decide
  rcases family_descends (prefixWord ++ tailWord_400445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400458 : List Nat := [3, 1, 2, 1, 1, 2, 2, 4, 2, 5]
def baseStart_400458 : Nat := 118140960795 + 400458 * 2 ^ 59
def prefixEnd_400458 : Nat := 4983230072969 + 3 ^ 40 * 400458 * 2
def baseEnd_400458 : Nat := 68542478646099813311111

theorem tailTrace_400458 : CollatzResearch.WordTrace tailWord_400458 prefixEnd_400458 68542478646099813311111 := by
  unfold tailWord_400458
  simp only [CollatzResearch.WordTrace]
  refine ⟨3651475795804133406620507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9737268788811022417654685 3651475795804133406620507)
  ·
    refine ⟨5477213693706200109930761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3651475795804133406620507 5477213693706200109930761)
    ·
      refine ⟨4107910270279650082448071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5477213693706200109930761 4107910270279650082448071)
      ·
        refine ⟨6161865405419475123672107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4107910270279650082448071 6161865405419475123672107)
        ·
          refine ⟨9242798108129212685508161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6161865405419475123672107 9242798108129212685508161)
          ·
            refine ⟨6932098581096909514131121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9242798108129212685508161 6932098581096909514131121)
            ·
              refine ⟨5199073935822682135598341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6932098581096909514131121 5199073935822682135598341)
              ·
                refine ⟨974826362966752900424689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5199073935822682135598341 974826362966752900424689)
                ·
                  refine ⟨731119772225064675318517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 974826362966752900424689 731119772225064675318517)
                  ·
                    refine ⟨68542478646099813311111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 731119772225064675318517 68542478646099813311111)
                    ·
                      rfl

theorem cell23_400458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_400458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400458 prefixEnd_400458 := by exact prefixLift 400458
  have htrace : WordTrace (prefixWord ++ tailWord_400458) baseStart_400458 baseEnd_400458 := by
    simpa [prefixWord, tailWord_400458, baseEnd_400458] using wordTrace_append hprefix tailTrace_400458
  have hstable : (prefixWord ++ tailWord_400458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400458).length < 2 ^ (prefixWord ++ tailWord_400458).sum := by decide
  have hdescent : baseEnd_400458 < baseStart_400458 := by decide
  rcases family_descends (prefixWord ++ tailWord_400458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400468 : List Nat := [2, 4, 1, 1, 1, 1, 2, 3, 1, 2, 5]
def baseStart_400468 : Nat := 118140960795 + 400468 * 2 ^ 59
def prefixEnd_400468 : Nat := 4983230072969 + 3 ^ 40 * 400468 * 2
def baseEnd_400468 : Nat := 205632570744844400808287

theorem tailTrace_400468 : CollatzResearch.WordTrace tailWord_400468 prefixEnd_400468 205632570744844400808287 := by
  unfold tailWord_400468
  simp only [CollatzResearch.WordTrace]
  refine ⟨7303133956590152667173029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9737511942120203556230705 7303133956590152667173029)
  ·
    refine ⟨1369337616860653625094943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7303133956590152667173029 1369337616860653625094943)
    ·
      refine ⟨2054006425290980437642415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1369337616860653625094943 2054006425290980437642415)
      ·
        refine ⟨3081009637936470656463623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2054006425290980437642415 3081009637936470656463623)
        ·
          refine ⟨4621514456904705984695435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3081009637936470656463623 4621514456904705984695435)
          ·
            refine ⟨6932271685357058977043153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4621514456904705984695435 6932271685357058977043153)
            ·
              refine ⟨5199203764017794232782365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6932271685357058977043153 5199203764017794232782365)
              ·
                refine ⟨1949701411506672837293387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5199203764017794232782365 1949701411506672837293387)
                ·
                  refine ⟨2924552117260009255940081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1949701411506672837293387 2924552117260009255940081)
                  ·
                    refine ⟨2193414087945006941955061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2924552117260009255940081 2193414087945006941955061)
                    ·
                      refine ⟨205632570744844400808287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2193414087945006941955061 205632570744844400808287)
                      ·
                        rfl

theorem cell23_400468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_400468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400468 prefixEnd_400468 := by exact prefixLift 400468
  have htrace : WordTrace (prefixWord ++ tailWord_400468) baseStart_400468 baseEnd_400468 := by
    simpa [prefixWord, tailWord_400468, baseEnd_400468] using wordTrace_append hprefix tailTrace_400468
  have hstable : (prefixWord ++ tailWord_400468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400468).length < 2 ^ (prefixWord ++ tailWord_400468).sum := by decide
  have hdescent : baseEnd_400468 < baseStart_400468 := by decide
  rcases family_descends (prefixWord ++ tailWord_400468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400515 : List Nat := [1, 1, 1, 3, 3, 2, 3, 2, 2, 2, 3]
def baseStart_400515 : Nat := 118140960795 + 400515 * 2 ^ 59
def prefixEnd_400515 : Nat := 4983230072969 + 3 ^ 40 * 400515 * 2
def baseEnd_400515 : Nat := 205656704335605716920571

theorem tailTrace_400515 : CollatzResearch.WordTrace tailWord_400515 prefixEnd_400515 205656704335605716920571 := by
  unfold tailWord_400515
  simp only [CollatzResearch.WordTrace]
  refine ⟨14607982144010032361306999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9738654762673354907537999 14607982144010032361306999)
  ·
    refine ⟨21911973216015048541960499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14607982144010032361306999 21911973216015048541960499)
    ·
      refine ⟨32867959824022572812940749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21911973216015048541960499 32867959824022572812940749)
      ·
        refine ⟨12325484934008464804852781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32867959824022572812940749 12325484934008464804852781)
        ·
          refine ⟨4622056850253174301819793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12325484934008464804852781 4622056850253174301819793)
          ·
            refine ⟨3466542637689880726364845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4622056850253174301819793 3466542637689880726364845)
            ·
              refine ⟨1299953489133705272386817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3466542637689880726364845 1299953489133705272386817)
              ·
                refine ⟨974965116850278954290113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1299953489133705272386817 974965116850278954290113)
                ·
                  refine ⟨731223837637709215717585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 974965116850278954290113 731223837637709215717585)
                  ·
                    refine ⟨548417878228281911788189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 731223837637709215717585 548417878228281911788189)
                    ·
                      refine ⟨205656704335605716920571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 548417878228281911788189 205656704335605716920571)
                      ·
                        rfl

theorem cell23_400515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2, 2, 3].length) (baseStart_400515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400515 prefixEnd_400515 := by exact prefixLift 400515
  have htrace : WordTrace (prefixWord ++ tailWord_400515) baseStart_400515 baseEnd_400515 := by
    simpa [prefixWord, tailWord_400515, baseEnd_400515] using wordTrace_append hprefix tailTrace_400515
  have hstable : (prefixWord ++ tailWord_400515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400515).length < 2 ^ (prefixWord ++ tailWord_400515).sum := by decide
  have hdescent : baseEnd_400515 < baseStart_400515 := by decide
  rcases family_descends (prefixWord ++ tailWord_400515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400528 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 3]
def baseStart_400528 : Nat := 118140960795 + 400528 * 2 ^ 59
def prefixEnd_400528 : Nat := 4983230072969 + 3 ^ 40 * 400528 * 2
def baseEnd_400528 : Nat := 205663379584114166058011

theorem tailTrace_400528 : CollatzResearch.WordTrace tailWord_400528 prefixEnd_400528 205663379584114166058011 := by
  unfold tailWord_400528
  simp only [CollatzResearch.WordTrace]
  refine ⟨7304228146481467790765119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9738970861975290387686825 7304228146481467790765119)
  ·
    refine ⟨10956342219722201686147679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7304228146481467790765119 10956342219722201686147679)
    ·
      refine ⟨16434513329583302529221519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10956342219722201686147679 16434513329583302529221519)
      ·
        refine ⟨24651769994374953793832279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16434513329583302529221519 24651769994374953793832279)
        ·
          refine ⟨36977654991562430690748419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24651769994374953793832279 36977654991562430690748419)
          ·
            refine ⟨55466482487343646036122629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36977654991562430690748419 55466482487343646036122629)
            ·
              refine ⟨10399965466376933631772993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55466482487343646036122629 10399965466376933631772993)
              ·
                refine ⟨7799974099782700223829745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10399965466376933631772993 7799974099782700223829745)
                ·
                  refine ⟨5849980574837025167872309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7799974099782700223829745 5849980574837025167872309)
                  ·
                    refine ⟨548435678890971109488029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5849980574837025167872309 548435678890971109488029)
                    ·
                      refine ⟨205663379584114166058011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 548435678890971109488029 205663379584114166058011)
                      ·
                        rfl

theorem cell23_400528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 3].length) (baseStart_400528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400528 prefixEnd_400528 := by exact prefixLift 400528
  have htrace : WordTrace (prefixWord ++ tailWord_400528) baseStart_400528 baseEnd_400528 := by
    simpa [prefixWord, tailWord_400528, baseEnd_400528] using wordTrace_append hprefix tailTrace_400528
  have hstable : (prefixWord ++ tailWord_400528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400528).length < 2 ^ (prefixWord ++ tailWord_400528).sum := by decide
  have hdescent : baseEnd_400528 < baseStart_400528 := by decide
  rcases family_descends (prefixWord ++ tailWord_400528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400535 : List Nat := [1, 1, 3, 3, 3, 2, 1, 3, 6]
def baseStart_400535 : Nat := 118140960795 + 400535 * 2 ^ 59
def prefixEnd_400535 : Nat := 4983230072969 + 3 ^ 40 * 400535 * 2
def baseEnd_400535 : Nat := 22851885994299515407831

theorem tailTrace_400535 : CollatzResearch.WordTrace tailWord_400535 prefixEnd_400535 22851885994299515407831 := by
  unfold tailWord_400535
  simp only [CollatzResearch.WordTrace]
  refine ⟨14608711603937575777035059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9739141069291717184690039 14608711603937575777035059)
  ·
    refine ⟨21913067405906363665552589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14608711603937575777035059 21913067405906363665552589)
    ·
      refine ⟨8217400277214886374582221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21913067405906363665552589 8217400277214886374582221)
      ·
        refine ⟨3081525103955582390468333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8217400277214886374582221 3081525103955582390468333)
        ·
          refine ⟨1155571913983343396425625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3081525103955582390468333 1155571913983343396425625)
          ·
            refine ⟨866678935487507547319219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1155571913983343396425625 866678935487507547319219)
            ·
              refine ⟨1300018403231261320978829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 866678935487507547319219 1300018403231261320978829)
              ·
                refine ⟨487506901211722995367061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1300018403231261320978829 487506901211722995367061)
                ·
                  refine ⟨22851885994299515407831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 487506901211722995367061 22851885994299515407831)
                  ·
                    rfl

theorem cell23_400535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3, 6].length) (baseStart_400535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400535 prefixEnd_400535 := by exact prefixLift 400535
  have htrace : WordTrace (prefixWord ++ tailWord_400535) baseStart_400535 baseEnd_400535 := by
    simpa [prefixWord, tailWord_400535, baseEnd_400535] using wordTrace_append hprefix tailTrace_400535
  have hstable : (prefixWord ++ tailWord_400535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400535).length < 2 ^ (prefixWord ++ tailWord_400535).sum := by decide
  have hdescent : baseEnd_400535 < baseStart_400535 := by decide
  rcases family_descends (prefixWord ++ tailWord_400535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400596 : List Nat := [2, 4, 1, 4, 1, 1, 1, 2, 3, 1, 3]
def baseStart_400596 : Nat := 118140960795 + 400596 * 2 ^ 59
def prefixEnd_400596 : Nat := 4983230072969 + 3 ^ 40 * 400596 * 2
def baseEnd_400596 : Nat := 205698296268619900007699

theorem tailTrace_400596 : CollatzResearch.WordTrace tailWord_400596 prefixEnd_400596 205698296268619900007699 := by
  unfold tailWord_400596
  simp only [CollatzResearch.WordTrace]
  refine ⟨7305468228358291597502821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9740624304477722130003761 7305468228358291597502821)
  ·
    refine ⟨1369775292817179674531779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7305468228358291597502821 1369775292817179674531779)
    ·
      refine ⟨2054662939225769511797669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1369775292817179674531779 2054662939225769511797669)
      ·
        refine ⟨385249301104831783462063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2054662939225769511797669 385249301104831783462063)
        ·
          refine ⟨577873951657247675193095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385249301104831783462063 577873951657247675193095)
          ·
            refine ⟨866810927485871512789643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 577873951657247675193095 866810927485871512789643)
            ·
              refine ⟨1300216391228807269184465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 866810927485871512789643 1300216391228807269184465)
              ·
                refine ⟨975162293421605451888349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1300216391228807269184465 975162293421605451888349)
                ·
                  refine ⟨365685860033102044458131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 975162293421605451888349 365685860033102044458131)
                  ·
                    refine ⟨548528790049653066687197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 365685860033102044458131 548528790049653066687197)
                    ·
                      refine ⟨205698296268619900007699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 548528790049653066687197 205698296268619900007699)
                      ·
                        rfl

theorem cell23_400596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_400596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400596 prefixEnd_400596 := by exact prefixLift 400596
  have htrace : WordTrace (prefixWord ++ tailWord_400596) baseStart_400596 baseEnd_400596 := by
    simpa [prefixWord, tailWord_400596, baseEnd_400596] using wordTrace_append hprefix tailTrace_400596
  have hstable : (prefixWord ++ tailWord_400596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400596).length < 2 ^ (prefixWord ++ tailWord_400596).sum := by decide
  have hdescent : baseEnd_400596 < baseStart_400596 := by decide
  rcases family_descends (prefixWord ++ tailWord_400596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400619 : List Nat := [1, 1, 1, 1, 2, 8, 2, 1, 1, 1, 4]
def baseStart_400619 : Nat := 118140960795 + 400619 * 2 ^ 59
def prefixEnd_400619 : Nat := 4983230072969 + 3 ^ 40 * 400619 * 2
def baseEnd_400619 : Nat := 205710106323673310020093

theorem tailTrace_400619 : CollatzResearch.WordTrace tailWord_400619 prefixEnd_400619 205710106323673310020093 := by
  unfold tailWord_400619
  simp only [CollatzResearch.WordTrace]
  refine ⟨14611775335633258123092911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9741183557088838748728607 14611775335633258123092911)
  ·
    refine ⟨21917663003449887184639367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14611775335633258123092911 21917663003449887184639367)
    ·
      refine ⟨32876494505174830776959051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21917663003449887184639367 32876494505174830776959051)
      ·
        refine ⟨49314741757762246165438577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32876494505174830776959051 49314741757762246165438577)
        ·
          refine ⟨36986056318321684624078933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49314741757762246165438577 36986056318321684624078933)
          ·
            refine ⟨433430347480332241688425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 36986056318321684624078933 433430347480332241688425)
            ·
              refine ⟨325072760610249181266319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 433430347480332241688425 325072760610249181266319)
              ·
                refine ⟨487609140915373771899479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 325072760610249181266319 487609140915373771899479)
                ·
                  refine ⟨731413711373060657849219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 487609140915373771899479 731413711373060657849219)
                  ·
                    refine ⟨1097120567059590986773829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 731413711373060657849219 1097120567059590986773829)
                    ·
                      refine ⟨205710106323673310020093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1097120567059590986773829 205710106323673310020093)
                      ·
                        rfl

theorem cell23_400619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 1, 1, 1, 4].length) (baseStart_400619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400619 prefixEnd_400619 := by exact prefixLift 400619
  have htrace : WordTrace (prefixWord ++ tailWord_400619) baseStart_400619 baseEnd_400619 := by
    simpa [prefixWord, tailWord_400619, baseEnd_400619] using wordTrace_append hprefix tailTrace_400619
  have hstable : (prefixWord ++ tailWord_400619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400619).length < 2 ^ (prefixWord ++ tailWord_400619).sum := by decide
  have hdescent : baseEnd_400619 < baseStart_400619 := by decide
  rcases family_descends (prefixWord ++ tailWord_400619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400636 : List Nat := [2, 2, 2, 1, 5, 1, 2, 1, 3, 2, 2]
def baseStart_400636 : Nat := 118140960795 + 400636 * 2 ^ 59
def prefixEnd_400636 : Nat := 4983230072969 + 3 ^ 40 * 400636 * 2
def baseEnd_400636 : Nat := 205718835494799743507515

theorem tailTrace_400636 : CollatzResearch.WordTrace tailWord_400636 prefixEnd_400636 205718835494799743507515 := by
  unfold tailWord_400636
  simp only [CollatzResearch.WordTrace]
  refine ⟨7306197688285835013230881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9741596917714446684307841 7306197688285835013230881)
  ·
    refine ⟨5479648266214376259923161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7306197688285835013230881 5479648266214376259923161)
    ·
      refine ⟨4109736199660782194942371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5479648266214376259923161 4109736199660782194942371)
      ·
        refine ⟨6164604299491173292413557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4109736199660782194942371 6164604299491173292413557)
        ·
          refine ⟨577931653077297496163771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6164604299491173292413557 577931653077297496163771)
          ·
            refine ⟨866897479615946244245657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 577931653077297496163771 866897479615946244245657)
            ·
              refine ⟨650173109711959683184243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 866897479615946244245657 650173109711959683184243)
              ·
                refine ⟨975259664567939524776365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 650173109711959683184243 975259664567939524776365)
                ·
                  refine ⟨365722374212977321791137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 975259664567939524776365 365722374212977321791137)
                  ·
                    refine ⟨274291780659732991343353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 365722374212977321791137 274291780659732991343353)
                    ·
                      refine ⟨205718835494799743507515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 274291780659732991343353 205718835494799743507515)
                      ·
                        rfl

theorem cell23_400636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 3, 2, 2].length) (baseStart_400636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400636 prefixEnd_400636 := by exact prefixLift 400636
  have htrace : WordTrace (prefixWord ++ tailWord_400636) baseStart_400636 baseEnd_400636 := by
    simpa [prefixWord, tailWord_400636, baseEnd_400636] using wordTrace_append hprefix tailTrace_400636
  have hstable : (prefixWord ++ tailWord_400636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400636).length < 2 ^ (prefixWord ++ tailWord_400636).sum := by decide
  have hdescent : baseEnd_400636 < baseStart_400636 := by decide
  rcases family_descends (prefixWord ++ tailWord_400636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400652 : List Nat := [2, 2, 1, 2, 2, 3, 3, 1, 1, 3, 3]
def baseStart_400652 : Nat := 118140960795 + 400652 * 2 ^ 59
def prefixEnd_400652 : Nat := 4983230072969 + 3 ^ 40 * 400652 * 2
def baseEnd_400652 : Nat := 205727051185271680907441

theorem tailTrace_400652 : CollatzResearch.WordTrace tailWord_400652 prefixEnd_400652 205727051185271680907441 := by
  unfold tailWord_400652
  simp only [CollatzResearch.WordTrace]
  refine ⟨7306489472256852379522105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9741985963009136506029473 7306489472256852379522105)
  ·
    refine ⟨5479867104192639284641579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7306489472256852379522105 5479867104192639284641579)
    ·
      refine ⟨8219800656288958926962369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5479867104192639284641579 8219800656288958926962369)
      ·
        refine ⟨6164850492216719195221777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8219800656288958926962369 6164850492216719195221777)
        ·
          refine ⟨4623637869162539396416333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6164850492216719195221777 4623637869162539396416333)
          ·
            refine ⟨1733864200935952273656125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4623637869162539396416333 1733864200935952273656125)
            ·
              refine ⟨650199075350982102621047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1733864200935952273656125 650199075350982102621047)
              ·
                refine ⟨975298613026473153931571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 650199075350982102621047 975298613026473153931571)
                ·
                  refine ⟨1462947919539709730897357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 975298613026473153931571 1462947919539709730897357)
                  ·
                    refine ⟨548605469827391149086509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1462947919539709730897357 548605469827391149086509)
                    ·
                      refine ⟨205727051185271680907441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 548605469827391149086509 205727051185271680907441)
                      ·
                        rfl

theorem cell23_400652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 1, 3, 3].length) (baseStart_400652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400652 prefixEnd_400652 := by exact prefixLift 400652
  have htrace : WordTrace (prefixWord ++ tailWord_400652) baseStart_400652 baseEnd_400652 := by
    simpa [prefixWord, tailWord_400652, baseEnd_400652] using wordTrace_append hprefix tailTrace_400652
  have hstable : (prefixWord ++ tailWord_400652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400652).length < 2 ^ (prefixWord ++ tailWord_400652).sum := by decide
  have hdescent : baseEnd_400652 < baseStart_400652 := by decide
  rcases family_descends (prefixWord ++ tailWord_400652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400669 : List Nat := [1, 4, 2, 3, 1, 1, 1, 2, 4, 1, 3]
def baseStart_400669 : Nat := 118140960795 + 400669 * 2 ^ 59
def prefixEnd_400669 : Nat := 4983230072969 + 3 ^ 40 * 400669 * 2
def baseEnd_400669 : Nat := 205735780356398114394863

theorem tailTrace_400669 : CollatzResearch.WordTrace tailWord_400669 prefixEnd_400669 205735780356398114394863 := by
  unfold tailWord_400669
  simp only [CollatzResearch.WordTrace]
  refine ⟨14613598985452116662413061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9742399323634744441608707 14613598985452116662413061)
  ·
    refine ⟨2740049809772271874202449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14613598985452116662413061 2740049809772271874202449)
    ·
      refine ⟨2055037357329203905651837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2740049809772271874202449 2055037357329203905651837)
      ·
        refine ⟨770639008998451464619439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2055037357329203905651837 770639008998451464619439)
        ·
          refine ⟨1155958513497677196929159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 770639008998451464619439 1155958513497677196929159)
          ·
            refine ⟨1733937770246515795393739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1155958513497677196929159 1733937770246515795393739)
            ·
              refine ⟨2600906655369773693090609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1733937770246515795393739 2600906655369773693090609)
              ·
                refine ⟨1950679991527330269817957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2600906655369773693090609 1950679991527330269817957)
                ·
                  refine ⟨365752498411374425590867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1950679991527330269817957 365752498411374425590867)
                  ·
                    refine ⟨548628747617061638386301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 365752498411374425590867 548628747617061638386301)
                    ·
                      refine ⟨205735780356398114394863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 548628747617061638386301 205735780356398114394863)
                      ·
                        rfl

theorem cell23_400669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_400669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400669 prefixEnd_400669 := by exact prefixLift 400669
  have htrace : WordTrace (prefixWord ++ tailWord_400669) baseStart_400669 baseEnd_400669 := by
    simpa [prefixWord, tailWord_400669, baseEnd_400669] using wordTrace_append hprefix tailTrace_400669
  have hstable : (prefixWord ++ tailWord_400669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400669).length < 2 ^ (prefixWord ++ tailWord_400669).sum := by decide
  have hdescent : baseEnd_400669 < baseStart_400669 := by decide
  rcases family_descends (prefixWord ++ tailWord_400669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400692 : List Nat := [2, 5, 1, 1, 1, 1, 2, 1, 2, 3, 4]
def baseStart_400692 : Nat := 118140960795 + 400692 * 2 ^ 59
def prefixEnd_400692 : Nat := 4983230072969 + 3 ^ 40 * 400692 * 2
def baseEnd_400692 : Nat := 205747590411451524407257

theorem tailTrace_400692 : CollatzResearch.WordTrace tailWord_400692 prefixEnd_400692 205747590411451524407257 := by
  unfold tailWord_400692
  simp only [CollatzResearch.WordTrace]
  refine ⟨7307218932184395795250165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9742958576245861060333553 7307218932184395795250165)
  ·
    refine ⟨685051774892287105804703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7307218932184395795250165 685051774892287105804703)
    ·
      refine ⟨1027577662338430658707055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 685051774892287105804703 1027577662338430658707055)
      ·
        refine ⟨1541366493507645988060583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1027577662338430658707055 1541366493507645988060583)
        ·
          refine ⟨2312049740261468982090875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1541366493507645988060583 2312049740261468982090875)
          ·
            refine ⟨3468074610392203473136313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2312049740261468982090875 3468074610392203473136313)
            ·
              refine ⟨2601055957794152604852235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3468074610392203473136313 2601055957794152604852235)
              ·
                refine ⟨3901583936691228907278353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2601055957794152604852235 3901583936691228907278353)
                ·
                  refine ⟨2926187952518421680458765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3901583936691228907278353 2926187952518421680458765)
                  ·
                    refine ⟨1097320482194408130172037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2926187952518421680458765 1097320482194408130172037)
                    ·
                      refine ⟨205747590411451524407257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1097320482194408130172037 205747590411451524407257)
                      ·
                        rfl

theorem cell23_400692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_400692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400692 prefixEnd_400692 := by exact prefixLift 400692
  have htrace : WordTrace (prefixWord ++ tailWord_400692) baseStart_400692 baseEnd_400692 := by
    simpa [prefixWord, tailWord_400692, baseEnd_400692] using wordTrace_append hprefix tailTrace_400692
  have hstable : (prefixWord ++ tailWord_400692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400692).length < 2 ^ (prefixWord ++ tailWord_400692).sum := by decide
  have hdescent : baseEnd_400692 < baseStart_400692 := by decide
  rcases family_descends (prefixWord ++ tailWord_400692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400743 : List Nat := [1, 1, 5, 1, 4, 1, 2, 2, 2, 2, 2]
def baseStart_400743 : Nat := 118140960795 + 400743 * 2 ^ 59
def prefixEnd_400743 : Nat := 4983230072969 + 3 ^ 40 * 400743 * 2
def baseEnd_400743 : Nat := 205773777924830824869523

theorem tailTrace_400743 : CollatzResearch.WordTrace tailWord_400743 prefixEnd_400743 205773777924830824869523 := by
  unfold tailWord_400743
  simp only [CollatzResearch.WordTrace]
  refine ⟨14616297987184027300606883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9744198658122684867071255 14616297987184027300606883)
  ·
    refine ⟨21924446980776040950910325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14616297987184027300606883 21924446980776040950910325)
    ·
      refine ⟨2055416904447753839147843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21924446980776040950910325 2055416904447753839147843)
      ·
        refine ⟨3083125356671630758721765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2055416904447753839147843 3083125356671630758721765)
        ·
          refine ⟨578086004375930767260331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3083125356671630758721765 578086004375930767260331)
          ·
            refine ⟨867129006563896150890497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 578086004375930767260331 867129006563896150890497)
            ·
              refine ⟨650346754922922113167873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 867129006563896150890497 650346754922922113167873)
              ·
                refine ⟨487760066192191584875905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 650346754922922113167873 487760066192191584875905)
                ·
                  refine ⟨365820049644143688656929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 487760066192191584875905 365820049644143688656929)
                  ·
                    refine ⟨274365037233107766492697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 365820049644143688656929 274365037233107766492697)
                    ·
                      refine ⟨205773777924830824869523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 274365037233107766492697 205773777924830824869523)
                      ·
                        rfl

theorem cell23_400743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2, 2, 2, 2].length) (baseStart_400743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400743 prefixEnd_400743 := by exact prefixLift 400743
  have htrace : WordTrace (prefixWord ++ tailWord_400743) baseStart_400743 baseEnd_400743 := by
    simpa [prefixWord, tailWord_400743, baseEnd_400743] using wordTrace_append hprefix tailTrace_400743
  have hstable : (prefixWord ++ tailWord_400743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400743).length < 2 ^ (prefixWord ++ tailWord_400743).sum := by decide
  have hdescent : baseEnd_400743 < baseStart_400743 := by decide
  rcases family_descends (prefixWord ++ tailWord_400743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400745 : List Nat := [1, 2, 1, 1, 1, 3, 2, 3, 4, 5]
def baseStart_400745 : Nat := 118140960795 + 400745 * 2 ^ 59
def prefixEnd_400745 : Nat := 4983230072969 + 3 ^ 40 * 400745 * 2
def baseEnd_400745 : Nat := 68591601628713272348171

theorem tailTrace_400745 : CollatzResearch.WordTrace tailWord_400745 prefixEnd_400745 68591601628713272348171 := by
  unfold tailWord_400745
  simp only [CollatzResearch.WordTrace]
  refine ⟨14616370933176781642179689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9744247288784521094786459 14616370933176781642179689)
  ·
    refine ⟨10962278199882586231634767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14616370933176781642179689 10962278199882586231634767)
    ·
      refine ⟨16443417299823879347452151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10962278199882586231634767 16443417299823879347452151)
      ·
        refine ⟨24665125949735819021178227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16443417299823879347452151 24665125949735819021178227)
        ·
          refine ⟨36997688924603728531767341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24665125949735819021178227 36997688924603728531767341)
          ·
            refine ⟨13874133346726398199412753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36997688924603728531767341 13874133346726398199412753)
            ·
              refine ⟨10405600010044798649559565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13874133346726398199412753 10405600010044798649559565)
              ·
                refine ⟨3902100003766799493584837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10405600010044798649559565 3902100003766799493584837)
                ·
                  refine ⟨731643750706274905047157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3902100003766799493584837 731643750706274905047157)
                  ·
                    refine ⟨68591601628713272348171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 731643750706274905047157 68591601628713272348171)
                    ·
                      rfl

theorem cell23_400745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4, 5].length) (baseStart_400745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400745 prefixEnd_400745 := by exact prefixLift 400745
  have htrace : WordTrace (prefixWord ++ tailWord_400745) baseStart_400745 baseEnd_400745 := by
    simpa [prefixWord, tailWord_400745, baseEnd_400745] using wordTrace_append hprefix tailTrace_400745
  have hstable : (prefixWord ++ tailWord_400745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400745).length < 2 ^ (prefixWord ++ tailWord_400745).sum := by decide
  have hdescent : baseEnd_400745 < baseStart_400745 := by decide
  rcases family_descends (prefixWord ++ tailWord_400745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400749 : List Nat := [1, 5, 1, 1, 1, 4, 1, 4, 5]
def baseStart_400749 : Nat := 118140960795 + 400749 * 2 ^ 59
def prefixEnd_400749 : Nat := 4983230072969 + 3 ^ 40 * 400749 * 2
def baseEnd_400749 : Nat := 22864095423195311266055

theorem tailTrace_400749 : CollatzResearch.WordTrace tailWord_400749 prefixEnd_400749 22864095423195311266055 := by
  unfold tailWord_400749
  simp only [CollatzResearch.WordTrace]
  refine ⟨14616516825162290325325301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9744344550108193550216867 14616516825162290325325301)
  ·
    refine ⟨1370298452358964717999247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14616516825162290325325301 1370298452358964717999247)
    ·
      refine ⟨2055447678538447076998871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1370298452358964717999247 2055447678538447076998871)
      ·
        refine ⟨3083171517807670615498307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2055447678538447076998871 3083171517807670615498307)
        ·
          refine ⟨4624757276711505923247461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3083171517807670615498307 4624757276711505923247461)
          ·
            refine ⟨867141989383407360608899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4624757276711505923247461 867141989383407360608899)
            ·
              refine ⟨1300712984075111040913349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 867141989383407360608899 1300712984075111040913349)
              ·
                refine ⟨243883684514083320171253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1300712984075111040913349 243883684514083320171253)
                ·
                  refine ⟨22864095423195311266055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 243883684514083320171253 22864095423195311266055)
                  ·
                    rfl

theorem cell23_400749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_400749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400749 prefixEnd_400749 := by exact prefixLift 400749
  have htrace : WordTrace (prefixWord ++ tailWord_400749) baseStart_400749 baseEnd_400749 := by
    simpa [prefixWord, tailWord_400749, baseEnd_400749] using wordTrace_append hprefix tailTrace_400749
  have hstable : (prefixWord ++ tailWord_400749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400749).length < 2 ^ (prefixWord ++ tailWord_400749).sum := by decide
  have hdescent : baseEnd_400749 < baseStart_400749 := by decide
  rcases family_descends (prefixWord ++ tailWord_400749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400752 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 1, 7, 2]
def baseStart_400752 : Nat := 118140960795 + 400752 * 2 ^ 59
def prefixEnd_400752 : Nat := 4983230072969 + 3 ^ 40 * 400752 * 2
def baseEnd_400752 : Nat := 205778399250721289656981

theorem tailTrace_400752 : CollatzResearch.WordTrace tailWord_400752 prefixEnd_400752 205778399250721289656981 := by
  unfold tailWord_400752
  simp only [CollatzResearch.WordTrace]
  refine ⟨7308313122075710918842255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9744417496100947891789673 7308313122075710918842255)
  ·
    refine ⟨10962469683113566378263383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7308313122075710918842255 10962469683113566378263383)
    ·
      refine ⟨16443704524670349567395075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10962469683113566378263383 16443704524670349567395075)
      ·
        refine ⟨24665556787005524351092613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16443704524670349567395075 24665556787005524351092613)
        ·
          refine ⟨4624791897563535815829865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24665556787005524351092613 4624791897563535815829865)
          ·
            refine ⟨3468593923172651861872399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4624791897563535815829865 3468593923172651861872399)
            ·
              refine ⟨5202890884758977792808599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3468593923172651861872399 5202890884758977792808599)
              ·
                refine ⟨7804336327138466689212899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5202890884758977792808599 7804336327138466689212899)
                ·
                  refine ⟨11706504490707700033819349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7804336327138466689212899 11706504490707700033819349)
                  ·
                    refine ⟨274371199000961719542641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11706504490707700033819349 274371199000961719542641)
                    ·
                      refine ⟨205778399250721289656981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 274371199000961719542641 205778399250721289656981)
                      ·
                        rfl

theorem cell23_400752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 1, 7, 2].length) (baseStart_400752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400752 prefixEnd_400752 := by exact prefixLift 400752
  have htrace : WordTrace (prefixWord ++ tailWord_400752) baseStart_400752 baseEnd_400752 := by
    simpa [prefixWord, tailWord_400752, baseEnd_400752] using wordTrace_append hprefix tailTrace_400752
  have hstable : (prefixWord ++ tailWord_400752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400752).length < 2 ^ (prefixWord ++ tailWord_400752).sum := by decide
  have hdescent : baseEnd_400752 < baseStart_400752 := by decide
  rcases family_descends (prefixWord ++ tailWord_400752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400766 : List Nat := [4, 2, 3, 2, 1, 1, 1, 2, 7]
def baseStart_400766 : Nat := 118140960795 + 400766 * 2 ^ 59
def prefixEnd_400766 : Nat := 4983230072969 + 3 ^ 40 * 400766 * 2
def baseEnd_400766 : Nat := 22865065331098248320213

theorem tailTrace_400766 : CollatzResearch.WordTrace tailWord_400766 prefixEnd_400766 22865065331098248320213 := by
  unfold tailWord_400766
  simp only [CollatzResearch.WordTrace]
  refine ⟨1827142108262587778586769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9744757910733801485796101 1827142108262587778586769)
  ·
    refine ⟨1370356581196940833940077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1827142108262587778586769 1370356581196940833940077)
    ·
      refine ⟨513883717948852812727529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1370356581196940833940077 513883717948852812727529)
      ·
        refine ⟨385412788461639609545647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 513883717948852812727529 385412788461639609545647)
        ·
          refine ⟨578119182692459414318471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385412788461639609545647 578119182692459414318471)
          ·
            refine ⟨867178774038689121477707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 578119182692459414318471 867178774038689121477707)
            ·
              refine ⟨1300768161058033682216561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 867178774038689121477707 1300768161058033682216561)
              ·
                refine ⟨975576120793525261662421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1300768161058033682216561 975576120793525261662421)
                ·
                  refine ⟨22865065331098248320213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 975576120793525261662421 22865065331098248320213)
                  ·
                    rfl

theorem cell23_400766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_400766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400766 prefixEnd_400766 := by exact prefixLift 400766
  have htrace : WordTrace (prefixWord ++ tailWord_400766) baseStart_400766 baseEnd_400766 := by
    simpa [prefixWord, tailWord_400766, baseEnd_400766] using wordTrace_append hprefix tailTrace_400766
  have hstable : (prefixWord ++ tailWord_400766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400766).length < 2 ^ (prefixWord ++ tailWord_400766).sum := by decide
  have hdescent : baseEnd_400766 < baseStart_400766 := by decide
  rcases family_descends (prefixWord ++ tailWord_400766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400795 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 6, 4, 4]
def baseStart_400795 : Nat := 118140960795 + 400795 * 2 ^ 59
def prefixEnd_400795 : Nat := 4983230072969 + 3 ^ 40 * 400795 * 2
def baseEnd_400795 : Nat := 205800478918864621419283

theorem tailTrace_400795 : CollatzResearch.WordTrace tailWord_400795 prefixEnd_400795 205800478918864621419283 := by
  unfold tailWord_400795
  simp only [CollatzResearch.WordTrace]
  refine ⟨14618194582995640181499839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9745463055330426787666559 14618194582995640181499839)
  ·
    refine ⟨21927291874493460272249759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14618194582995640181499839 21927291874493460272249759)
    ·
      refine ⟨32890937811740190408374639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21927291874493460272249759 32890937811740190408374639)
      ·
        refine ⟨49336406717610285612561959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32890937811740190408374639 49336406717610285612561959)
        ·
          refine ⟨74004610076415428418842939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49336406717610285612561959 74004610076415428418842939)
          ·
            refine ⟨111006915114623142628264409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74004610076415428418842939 111006915114623142628264409)
            ·
              refine ⟨83255186335967356971198307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111006915114623142628264409 83255186335967356971198307)
              ·
                refine ⟨124882779503951035456797461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83255186335967356971198307 124882779503951035456797461)
                ·
                  refine ⟨5853880289247704787037381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 124882779503951035456797461 5853880289247704787037381)
                  ·
                    refine ⟨1097602554233944647569509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5853880289247704787037381 1097602554233944647569509)
                    ·
                      refine ⟨205800478918864621419283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1097602554233944647569509 205800478918864621419283)
                      ·
                        rfl

theorem cell23_400795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4, 4].length) (baseStart_400795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400795 prefixEnd_400795 := by exact prefixLift 400795
  have htrace : WordTrace (prefixWord ++ tailWord_400795) baseStart_400795 baseEnd_400795 := by
    simpa [prefixWord, tailWord_400795, baseEnd_400795] using wordTrace_append hprefix tailTrace_400795
  have hstable : (prefixWord ++ tailWord_400795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400795).length < 2 ^ (prefixWord ++ tailWord_400795).sum := by decide
  have hdescent : baseEnd_400795 < baseStart_400795 := by decide
  rcases family_descends (prefixWord ++ tailWord_400795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400799 : List Nat := [1, 1, 2, 5, 1, 2, 1, 2, 2, 4, 2]
def baseStart_400799 : Nat := 118140960795 + 400799 * 2 ^ 59
def prefixEnd_400799 : Nat := 4983230072969 + 3 ^ 40 * 400799 * 2
def baseEnd_400799 : Nat := 205802532841482605769265

theorem tailTrace_400799 : CollatzResearch.WordTrace tailWord_400799 prefixEnd_400799 205802532841482605769265 := by
  unfold tailWord_400799
  simp only [CollatzResearch.WordTrace]
  refine ⟨14618340474981148864645451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9745560316654099243096967 14618340474981148864645451)
  ·
    refine ⟨21927510712471723296968177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14618340474981148864645451 21927510712471723296968177)
    ·
      refine ⟨16445633034353792472726133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21927510712471723296968177 16445633034353792472726133)
      ·
        refine ⟨1541778096970668044318075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16445633034353792472726133 1541778096970668044318075)
        ·
          refine ⟨2312667145456002066477113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1541778096970668044318075 2312667145456002066477113)
          ·
            refine ⟨1734500359092001549857835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2312667145456002066477113 1734500359092001549857835)
            ·
              refine ⟨2601750538638002324786753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1734500359092001549857835 2601750538638002324786753)
              ·
                refine ⟨1951312903978501743590065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2601750538638002324786753 1951312903978501743590065)
                ·
                  refine ⟨1463484677983876307692549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1951312903978501743590065 1463484677983876307692549)
                  ·
                    refine ⟨274403377121976807692353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1463484677983876307692549 274403377121976807692353)
                    ·
                      refine ⟨205802532841482605769265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 274403377121976807692353 205802532841482605769265)
                      ·
                        rfl

theorem cell23_400799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_400799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400799 prefixEnd_400799 := by exact prefixLift 400799
  have htrace : WordTrace (prefixWord ++ tailWord_400799) baseStart_400799 baseEnd_400799 := by
    simpa [prefixWord, tailWord_400799, baseEnd_400799] using wordTrace_append hprefix tailTrace_400799
  have hstable : (prefixWord ++ tailWord_400799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400799).length < 2 ^ (prefixWord ++ tailWord_400799).sum := by decide
  have hdescent : baseEnd_400799 < baseStart_400799 := by decide
  rcases family_descends (prefixWord ++ tailWord_400799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400834 : List Nat := [3, 5, 2, 1, 2, 1, 1, 3, 5]
def baseStart_400834 : Nat := 118140960795 + 400834 * 2 ^ 59
def prefixEnd_400834 : Nat := 4983230072969 + 3 ^ 40 * 400834 * 2
def baseEnd_400834 : Nat := 22868944962709996536845

theorem tailTrace_400834 : CollatzResearch.WordTrace tailWord_400834 prefixEnd_400834 22868944962709996536845 := by
  unfold tailWord_400834
  simp only [CollatzResearch.WordTrace]
  refine ⟨3654904257463587460542389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9746411353236233228113037 3654904257463587460542389)
  ·
    refine ⟨342647274137211324425849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3654904257463587460542389 342647274137211324425849)
    ·
      refine ⟨256985455602908493319387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342647274137211324425849 256985455602908493319387)
      ·
        refine ⟨385478183404362739979081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256985455602908493319387 385478183404362739979081)
        ·
          refine ⟨289108637553272054984311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385478183404362739979081 289108637553272054984311)
          ·
            refine ⟨433662956329908082476467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289108637553272054984311 433662956329908082476467)
            ·
              refine ⟨650494434494862123714701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433662956329908082476467 650494434494862123714701)
              ·
                refine ⟨243935412935573296393013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 650494434494862123714701 243935412935573296393013)
                ·
                  refine ⟨22868944962709996536845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 243935412935573296393013 22868944962709996536845)
                  ·
                    rfl

theorem cell23_400834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_400834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400834 prefixEnd_400834 := by exact prefixLift 400834
  have htrace : WordTrace (prefixWord ++ tailWord_400834) baseStart_400834 baseEnd_400834 := by
    simpa [prefixWord, tailWord_400834, baseEnd_400834] using wordTrace_append hprefix tailTrace_400834
  have hstable : (prefixWord ++ tailWord_400834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400834).length < 2 ^ (prefixWord ++ tailWord_400834).sum := by decide
  have hdescent : baseEnd_400834 < baseStart_400834 := by decide
  rcases family_descends (prefixWord ++ tailWord_400834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400886 : List Nat := [5, 1, 1, 1, 2, 2, 3, 2, 1, 5]
def baseStart_400886 : Nat := 118140960795 + 400886 * 2 ^ 59
def prefixEnd_400886 : Nat := 4983230072969 + 3 ^ 40 * 400886 * 2
def baseEnd_400886 : Nat := 68615735219474588460455

theorem tailTrace_400886 : CollatzResearch.WordTrace tailWord_400886 prefixEnd_400886 68615735219474588460455 := by
  unfold tailWord_400886
  simp only [CollatzResearch.WordTrace]
  refine ⟨913844601604122670191407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9747675750443975148708341 913844601604122670191407)
  ·
    refine ⟨1370766902406184005287111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 913844601604122670191407 1370766902406184005287111)
    ·
      refine ⟨2056150353609276007930667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1370766902406184005287111 2056150353609276007930667)
      ·
        refine ⟨3084225530413914011896001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2056150353609276007930667 3084225530413914011896001)
        ·
          refine ⟨2313169147810435508922001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3084225530413914011896001 2313169147810435508922001)
          ·
            refine ⟨1734876860857826631691501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2313169147810435508922001 1734876860857826631691501)
            ·
              refine ⟨650578822821684986884313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1734876860857826631691501 650578822821684986884313)
              ·
                refine ⟨487934117116263740163235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 650578822821684986884313 487934117116263740163235)
                ·
                  refine ⟨731901175674395610244853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 487934117116263740163235 731901175674395610244853)
                  ·
                    refine ⟨68615735219474588460455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 731901175674395610244853 68615735219474588460455)
                    ·
                      rfl

theorem cell23_400886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_400886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400886 prefixEnd_400886 := by exact prefixLift 400886
  have htrace : WordTrace (prefixWord ++ tailWord_400886) baseStart_400886 baseEnd_400886 := by
    simpa [prefixWord, tailWord_400886, baseEnd_400886] using wordTrace_append hprefix tailTrace_400886
  have hstable : (prefixWord ++ tailWord_400886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400886).length < 2 ^ (prefixWord ++ tailWord_400886).sum := by decide
  have hdescent : baseEnd_400886 < baseStart_400886 := by decide
  rcases family_descends (prefixWord ++ tailWord_400886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400892 : List Nat := [2, 2, 2, 1, 2, 1, 2, 2, 3, 1, 5]
def baseStart_400892 : Nat := 118140960795 + 400892 * 2 ^ 59
def prefixEnd_400892 : Nat := 4983230072969 + 3 ^ 40 * 400892 * 2
def baseEnd_400892 : Nat := 205850286542350741906337

theorem tailTrace_400892 : CollatzResearch.WordTrace tailWord_400892 prefixEnd_400892 205850286542350741906337 := by
  unfold tailWord_400892
  simp only [CollatzResearch.WordTrace]
  refine ⟨7310866231822112873890465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9747821642429483831853953 7310866231822112873890465)
  ·
    refine ⟨5483149673866584655417849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7310866231822112873890465 5483149673866584655417849)
    ·
      refine ⟨4112362255399938491563387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5483149673866584655417849 4112362255399938491563387)
      ·
        refine ⟨6168543383099907737345081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4112362255399938491563387 6168543383099907737345081)
        ·
          refine ⟨4626407537324930803008811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6168543383099907737345081 4626407537324930803008811)
          ·
            refine ⟨6939611305987396204513217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4626407537324930803008811 6939611305987396204513217)
            ·
              refine ⟨5204708479490547153384913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6939611305987396204513217 5204708479490547153384913)
              ·
                refine ⟨3903531359617910365038685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5204708479490547153384913 3903531359617910365038685)
                ·
                  refine ⟨1463824259856716386889507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3903531359617910365038685 1463824259856716386889507)
                  ·
                    refine ⟨2195736389785074580334261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1463824259856716386889507 2195736389785074580334261)
                    ·
                      refine ⟨205850286542350741906337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2195736389785074580334261 205850286542350741906337)
                      ·
                        rfl

theorem cell23_400892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_400892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400892 prefixEnd_400892 := by exact prefixLift 400892
  have htrace : WordTrace (prefixWord ++ tailWord_400892) baseStart_400892 baseEnd_400892 := by
    simpa [prefixWord, tailWord_400892, baseEnd_400892] using wordTrace_append hprefix tailTrace_400892
  have hstable : (prefixWord ++ tailWord_400892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400892).length < 2 ^ (prefixWord ++ tailWord_400892).sum := by decide
  have hdescent : baseEnd_400892 < baseStart_400892 := by decide
  rcases family_descends (prefixWord ++ tailWord_400892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400929 : List Nat := [1, 2, 3, 2, 2, 4, 1, 8]
def baseStart_400929 : Nat := 118140960795 + 400929 * 2 ^ 59
def prefixEnd_400929 : Nat := 4983230072969 + 3 ^ 40 * 400929 * 2
def baseEnd_400929 : Nat := 7624788345428411005321

theorem tailTrace_400929 : CollatzResearch.WordTrace tailWord_400929 prefixEnd_400929 7624788345428411005321 := by
  unfold tailWord_400929
  simp only [CollatzResearch.WordTrace]
  refine ⟨14623081964510181066877841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9748721309673454044585227 14623081964510181066877841)
  ·
    refine ⟨10967311473382635800158381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14623081964510181066877841 10967311473382635800158381)
    ·
      refine ⟨4112741802518488425059393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10967311473382635800158381 4112741802518488425059393)
      ·
        refine ⟨3084556351888866318794545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4112741802518488425059393 3084556351888866318794545)
        ·
          refine ⟨2313417263916649739095909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3084556351888866318794545 2313417263916649739095909)
          ·
            refine ⟨433765736984371826080483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2313417263916649739095909 433765736984371826080483)
            ·
              refine ⟨650648605476557739120725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433765736984371826080483 650648605476557739120725)
              ·
                refine ⟨7624788345428411005321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 650648605476557739120725 7624788345428411005321)
                ·
                  rfl

theorem cell23_400929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 8].length) (baseStart_400929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400929 prefixEnd_400929 := by exact prefixLift 400929
  have htrace : WordTrace (prefixWord ++ tailWord_400929) baseStart_400929 baseEnd_400929 := by
    simpa [prefixWord, tailWord_400929, baseEnd_400929] using wordTrace_append hprefix tailTrace_400929
  have hstable : (prefixWord ++ tailWord_400929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400929).length < 2 ^ (prefixWord ++ tailWord_400929).sum := by decide
  have hdescent : baseEnd_400929 < baseStart_400929 := by decide
  rcases family_descends (prefixWord ++ tailWord_400929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400939 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 8, 1, 3]
def baseStart_400939 : Nat := 118140960795 + 400939 * 2 ^ 59
def prefixEnd_400939 : Nat := 4983230072969 + 3 ^ 40 * 400939 * 2
def baseEnd_400939 : Nat := 205874420133112058018621

theorem tailTrace_400939 : CollatzResearch.WordTrace tailWord_400939 prefixEnd_400939 205874420133112058018621 := by
  unfold tailWord_400939
  simp only [CollatzResearch.WordTrace]
  refine ⟨14623446694473952774741871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9748964462982635183161247 14623446694473952774741871)
  ·
    refine ⟨21935170041710929162112807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14623446694473952774741871 21935170041710929162112807)
    ·
      refine ⟨32902755062566393743169211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21935170041710929162112807 32902755062566393743169211)
      ·
        refine ⟨49354132593849590614753817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32902755062566393743169211 49354132593849590614753817)
        ·
          refine ⟨37015599445387192961065363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49354132593849590614753817 37015599445387192961065363)
          ·
            refine ⟨55523399168080789441598045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37015599445387192961065363 55523399168080789441598045)
            ·
              refine ⟨20821274688030296040599267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55523399168080789441598045 20821274688030296040599267)
              ·
                refine ⟨31231912032045444060898901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20821274688030296040599267 31231912032045444060898901)
                ·
                  refine ⟨365998969125532547588659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31231912032045444060898901 365998969125532547588659)
                  ·
                    refine ⟨548998453688298821382989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 365998969125532547588659 548998453688298821382989)
                    ·
                      refine ⟨205874420133112058018621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 548998453688298821382989 205874420133112058018621)
                      ·
                        rfl

theorem cell23_400939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 8, 1, 3].length) (baseStart_400939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400939 prefixEnd_400939 := by exact prefixLift 400939
  have htrace : WordTrace (prefixWord ++ tailWord_400939) baseStart_400939 baseEnd_400939 := by
    simpa [prefixWord, tailWord_400939, baseEnd_400939] using wordTrace_append hprefix tailTrace_400939
  have hstable : (prefixWord ++ tailWord_400939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400939).length < 2 ^ (prefixWord ++ tailWord_400939).sum := by decide
  have hdescent : baseEnd_400939 < baseStart_400939 := by decide
  rcases family_descends (prefixWord ++ tailWord_400939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400957 : List Nat := [1, 4, 1, 3, 3, 1, 2, 3, 1, 2, 2]
def baseStart_400957 : Nat := 118140960795 + 400957 * 2 ^ 59
def prefixEnd_400957 : Nat := 4983230072969 + 3 ^ 40 * 400957 * 2
def baseEnd_400957 : Nat := 205883662784892987593539

theorem tailTrace_400957 : CollatzResearch.WordTrace tailWord_400957 prefixEnd_400957 205883662784892987593539 := by
  unfold tailWord_400957
  simp only [CollatzResearch.WordTrace]
  refine ⟨14624103208408741848897125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9749402138939161232598083 14624103208408741848897125)
  ·
    refine ⟨2742019351576639096668211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14624103208408741848897125 2742019351576639096668211)
    ·
      refine ⟨4113029027364958645002317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2742019351576639096668211 4113029027364958645002317)
      ·
        refine ⟨1542385885261859491875869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4113029027364958645002317 1542385885261859491875869)
        ·
          refine ⟨578394706973197309453451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1542385885261859491875869 578394706973197309453451)
          ·
            refine ⟨867592060459795964180177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 578394706973197309453451 867592060459795964180177)
            ·
              refine ⟨650694045344846973135133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 867592060459795964180177 650694045344846973135133)
              ·
                refine ⟨244010267004317614925675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 650694045344846973135133 244010267004317614925675)
                ·
                  refine ⟨366015400506476422388513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 244010267004317614925675 366015400506476422388513)
                  ·
                    refine ⟨274511550379857316791385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 366015400506476422388513 274511550379857316791385)
                    ·
                      refine ⟨205883662784892987593539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 274511550379857316791385 205883662784892987593539)
                      ·
                        rfl

theorem cell23_400957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_400957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400957 prefixEnd_400957 := by exact prefixLift 400957
  have htrace : WordTrace (prefixWord ++ tailWord_400957) baseStart_400957 baseEnd_400957 := by
    simpa [prefixWord, tailWord_400957, baseEnd_400957] using wordTrace_append hprefix tailTrace_400957
  have hstable : (prefixWord ++ tailWord_400957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400957).length < 2 ^ (prefixWord ++ tailWord_400957).sum := by decide
  have hdescent : baseEnd_400957 < baseStart_400957 := by decide
  rcases family_descends (prefixWord ++ tailWord_400957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400999 : List Nat := [1, 1, 5, 1, 1, 1, 2, 2, 2, 4, 3]
def baseStart_400999 : Nat := 118140960795 + 400999 * 2 ^ 59
def prefixEnd_400999 : Nat := 4983230072969 + 3 ^ 40 * 400999 * 2
def baseEnd_400999 : Nat := 205905228972381823268345

theorem tailTrace_400999 : CollatzResearch.WordTrace tailWord_400999 prefixEnd_400999 205905228972381823268345 := by
  unfold tailWord_400999
  simp only [CollatzResearch.WordTrace]
  refine ⟨14625635074256583021926051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9750423382837722014617367 14625635074256583021926051)
  ·
    refine ⟨21938452611384874532889077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14625635074256583021926051 21938452611384874532889077)
    ·
      refine ⟨2056729932317331987458351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21938452611384874532889077 2056729932317331987458351)
      ·
        refine ⟨3085094898475997981187527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2056729932317331987458351 3085094898475997981187527)
        ·
          refine ⟨4627642347713996971781291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3085094898475997981187527 4627642347713996971781291)
          ·
            refine ⟨6941463521570995457671937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4627642347713996971781291 6941463521570995457671937)
            ·
              refine ⟨5206097641178246593253953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6941463521570995457671937 5206097641178246593253953)
              ·
                refine ⟨3904573230883684944940465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5206097641178246593253953 3904573230883684944940465)
                ·
                  refine ⟨2928429923162763708705349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3904573230883684944940465 2928429923162763708705349)
                  ·
                    refine ⟨549080610593018195382253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2928429923162763708705349 549080610593018195382253)
                    ·
                      refine ⟨205905228972381823268345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 549080610593018195382253 205905228972381823268345)
                      ·
                        rfl

theorem cell23_400999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_400999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_400999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_400999 prefixEnd_400999 := by exact prefixLift 400999
  have htrace : WordTrace (prefixWord ++ tailWord_400999) baseStart_400999 baseEnd_400999 := by
    simpa [prefixWord, tailWord_400999, baseEnd_400999] using wordTrace_append hprefix tailTrace_400999
  have hstable : (prefixWord ++ tailWord_400999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400999).length < 2 ^ (prefixWord ++ tailWord_400999).sum := by decide
  have hdescent : baseEnd_400999 < baseStart_400999 := by decide
  rcases family_descends (prefixWord ++ tailWord_400999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401000 : List Nat := [2, 1, 4, 3, 1, 2, 2, 2, 1, 3, 2]
def baseStart_401000 : Nat := 118140960795 + 401000 * 2 ^ 59
def prefixEnd_401000 : Nat := 4983230072969 + 3 ^ 40 * 401000 * 2
def baseEnd_401000 : Nat := 205905742453036319355841

theorem tailTrace_401000 : CollatzResearch.WordTrace tailWord_401000 prefixEnd_401000 205905742453036319355841 := by
  unfold tailWord_401000
  simp only [CollatzResearch.WordTrace]
  refine ⟨7312835773626480096356227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9750447698168640128474969 7312835773626480096356227)
  ·
    refine ⟨10969253660439720144534341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7312835773626480096356227 10969253660439720144534341)
    ·
      refine ⟨2056735061332447527100189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10969253660439720144534341 2056735061332447527100189)
      ·
        refine ⟨771275647999667822662571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2056735061332447527100189 771275647999667822662571)
        ·
          refine ⟨1156913471999501733993857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 771275647999667822662571 1156913471999501733993857)
          ·
            refine ⟨867685103999626300495393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1156913471999501733993857 867685103999626300495393)
            ·
              refine ⟨650763827999719725371545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 867685103999626300495393 650763827999719725371545)
              ·
                refine ⟨488072870999789794028659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 650763827999719725371545 488072870999789794028659)
                ·
                  refine ⟨732109306499684691042989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 488072870999789794028659 732109306499684691042989)
                  ·
                    refine ⟨274540989937381759141121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 732109306499684691042989 274540989937381759141121)
                    ·
                      refine ⟨205905742453036319355841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 274540989937381759141121 205905742453036319355841)
                      ·
                        rfl

theorem cell23_401000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_401000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401000 prefixEnd_401000 := by exact prefixLift 401000
  have htrace : WordTrace (prefixWord ++ tailWord_401000) baseStart_401000 baseEnd_401000 := by
    simpa [prefixWord, tailWord_401000, baseEnd_401000] using wordTrace_append hprefix tailTrace_401000
  have hstable : (prefixWord ++ tailWord_401000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401000).length < 2 ^ (prefixWord ++ tailWord_401000).sum := by decide
  have hdescent : baseEnd_401000 < baseStart_401000 := by decide
  rcases family_descends (prefixWord ++ tailWord_401000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401047 : List Nat := [1, 1, 3, 3, 2, 4, 2, 1, 2, 2, 2]
def baseStart_401047 : Nat := 118140960795 + 401047 * 2 ^ 59
def prefixEnd_401047 : Nat := 4983230072969 + 3 ^ 40 * 401047 * 2
def baseEnd_401047 : Nat := 205929876043797635468125

theorem tailTrace_401047 : CollatzResearch.WordTrace tailWord_401047 prefixEnd_401047 205929876043797635468125 := by
  unfold tailWord_401047
  simp only [CollatzResearch.WordTrace]
  refine ⟨14627385778082687219673395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9751590518721791479782263 14627385778082687219673395)
  ·
    refine ⟨21941078667124030829510093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14627385778082687219673395 21941078667124030829510093)
    ·
      refine ⟨8227904500171511561066285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21941078667124030829510093 8227904500171511561066285)
      ·
        refine ⟨3085464187564316835399857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8227904500171511561066285 3085464187564316835399857)
        ·
          refine ⟨2314098140673237626549893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3085464187564316835399857 2314098140673237626549893)
          ·
            refine ⟨433893401376232054978105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2314098140673237626549893 433893401376232054978105)
            ·
              refine ⟨325420051032174041233579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 433893401376232054978105 325420051032174041233579)
              ·
                refine ⟨488130076548261061850369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 325420051032174041233579 488130076548261061850369)
                ·
                  refine ⟨366097557411195796387777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 488130076548261061850369 366097557411195796387777)
                  ·
                    refine ⟨274573168058396847290833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 366097557411195796387777 274573168058396847290833)
                    ·
                      refine ⟨205929876043797635468125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 274573168058396847290833 205929876043797635468125)
                      ·
                        rfl

theorem cell23_401047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 1, 2, 2, 2].length) (baseStart_401047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401047 prefixEnd_401047 := by exact prefixLift 401047
  have htrace : WordTrace (prefixWord ++ tailWord_401047) baseStart_401047 baseEnd_401047 := by
    simpa [prefixWord, tailWord_401047, baseEnd_401047] using wordTrace_append hprefix tailTrace_401047
  have hstable : (prefixWord ++ tailWord_401047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401047).length < 2 ^ (prefixWord ++ tailWord_401047).sum := by decide
  have hdescent : baseEnd_401047 < baseStart_401047 := by decide
  rcases family_descends (prefixWord ++ tailWord_401047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401096 : List Nat := [2, 1, 3, 1, 2, 2, 2, 3, 3, 4]
def baseStart_401096 : Nat := 118140960795 + 401096 * 2 ^ 59
def prefixEnd_401096 : Nat := 4983230072969 + 3 ^ 40 * 401096 * 2
def baseEnd_401096 : Nat := 68651678865289314585133

theorem tailTrace_401096 : CollatzResearch.WordTrace tailWord_401096 prefixEnd_401096 68651678865289314585133 := by
  unfold tailWord_401096
  simp only [CollatzResearch.WordTrace]
  refine ⟨7314586477452584294103571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9752781969936779058804761 7314586477452584294103571)
  ·
    refine ⟨10971879716178876441155357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7314586477452584294103571 10971879716178876441155357)
    ·
      refine ⟨4114454893567078665433259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10971879716178876441155357 4114454893567078665433259)
      ·
        refine ⟨6171682340350617998149889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4114454893567078665433259 6171682340350617998149889)
        ·
          refine ⟨4628761755262963498612417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6171682340350617998149889 4628761755262963498612417)
          ·
            refine ⟨3471571316447222623959313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4628761755262963498612417 3471571316447222623959313)
            ·
              refine ⟨2603678487335416967969485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3471571316447222623959313 2603678487335416967969485)
              ·
                refine ⟨976379432750781362988557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2603678487335416967969485 976379432750781362988557)
                ·
                  refine ⟨366142287281543011120709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 976379432750781362988557 366142287281543011120709)
                  ·
                    refine ⟨68651678865289314585133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 366142287281543011120709 68651678865289314585133)
                    ·
                      rfl

theorem cell23_401096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 3, 4].length) (baseStart_401096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401096 prefixEnd_401096 := by exact prefixLift 401096
  have htrace : WordTrace (prefixWord ++ tailWord_401096) baseStart_401096 baseEnd_401096 := by
    simpa [prefixWord, tailWord_401096, baseEnd_401096] using wordTrace_append hprefix tailTrace_401096
  have hstable : (prefixWord ++ tailWord_401096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401096).length < 2 ^ (prefixWord ++ tailWord_401096).sum := by decide
  have hdescent : baseEnd_401096 < baseStart_401096 := by decide
  rcases family_descends (prefixWord ++ tailWord_401096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401117 : List Nat := [1, 4, 3, 3, 2, 1, 1, 1, 2, 5]
def baseStart_401117 : Nat := 118140960795 + 401117 * 2 ^ 59
def prefixEnd_401117 : Nat := 4983230072969 + 3 ^ 40 * 401117 * 2
def baseEnd_401117 : Nat := 68655273229870787197601

theorem tailTrace_401117 : CollatzResearch.WordTrace tailWord_401117 prefixEnd_401117 68655273229870787197601 := by
  unfold tailWord_401117
  simp only [CollatzResearch.WordTrace]
  refine ⟨14629938887829089174721605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9753292591886059449814403 14629938887829089174721605)
  ·
    refine ⟨2743113541467954220260301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14629938887829089174721605 2743113541467954220260301)
    ·
      refine ⟨1028667578050482832597613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2743113541467954220260301 1028667578050482832597613)
      ·
        refine ⟨385750341768931062224105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1028667578050482832597613 385750341768931062224105)
        ·
          refine ⟨289312756326698296668079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385750341768931062224105 289312756326698296668079)
          ·
            refine ⟨433969134490047445002119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289312756326698296668079 433969134490047445002119)
            ·
              refine ⟨650953701735071167503179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433969134490047445002119 650953701735071167503179)
              ·
                refine ⟨976430552602606751254769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 650953701735071167503179 976430552602606751254769)
                ·
                  refine ⟨732322914451955063441077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 976430552602606751254769 732322914451955063441077)
                  ·
                    refine ⟨68655273229870787197601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 732322914451955063441077 68655273229870787197601)
                    ·
                      rfl

theorem cell23_401117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_401117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401117 prefixEnd_401117 := by exact prefixLift 401117
  have htrace : WordTrace (prefixWord ++ tailWord_401117) baseStart_401117 baseEnd_401117 := by
    simpa [prefixWord, tailWord_401117, baseEnd_401117] using wordTrace_append hprefix tailTrace_401117
  have hstable : (prefixWord ++ tailWord_401117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401117).length < 2 ^ (prefixWord ++ tailWord_401117).sum := by decide
  have hdescent : baseEnd_401117 < baseStart_401117 := by decide
  rcases family_descends (prefixWord ++ tailWord_401117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401123 : List Nat := [1, 1, 1, 7, 2, 1, 1, 1, 1, 4, 3]
def baseStart_401123 : Nat := 118140960795 + 401123 * 2 ^ 59
def prefixEnd_401123 : Nat := 4983230072969 + 3 ^ 40 * 401123 * 2
def baseEnd_401123 : Nat := 205968900573539338117775

theorem tailTrace_401123 : CollatzResearch.WordTrace tailWord_401123 prefixEnd_401123 205968900573539338117775 := by
  unfold tailWord_401123
  simp only [CollatzResearch.WordTrace]
  refine ⟨14630157725807352199440023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9753438483871568132960015 14630157725807352199440023)
  ·
    refine ⟨21945236588711028299160035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14630157725807352199440023 21945236588711028299160035)
    ·
      refine ⟨32917854883066542448740053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21945236588711028299160035 32917854883066542448740053)
      ·
        refine ⟨771512223821872088642345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 32917854883066542448740053 771512223821872088642345)
        ·
          refine ⟨578634167866404066481759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 771512223821872088642345 578634167866404066481759)
          ·
            refine ⟨867951251799606099722639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 578634167866404066481759 867951251799606099722639)
            ·
              refine ⟨1301926877699409149583959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 867951251799606099722639 1301926877699409149583959)
              ·
                refine ⟨1952890316549113724375939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1301926877699409149583959 1952890316549113724375939)
                ·
                  refine ⟨2929335474823670586563909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1952890316549113724375939 2929335474823670586563909)
                  ·
                    refine ⟨549250401529438234980733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2929335474823670586563909 549250401529438234980733)
                    ·
                      refine ⟨205968900573539338117775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 549250401529438234980733 205968900573539338117775)
                      ·
                        rfl

theorem cell23_401123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_401123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401123 prefixEnd_401123 := by exact prefixLift 401123
  have htrace : WordTrace (prefixWord ++ tailWord_401123) baseStart_401123 baseEnd_401123 := by
    simpa [prefixWord, tailWord_401123, baseEnd_401123] using wordTrace_append hprefix tailTrace_401123
  have hstable : (prefixWord ++ tailWord_401123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401123).length < 2 ^ (prefixWord ++ tailWord_401123).sum := by decide
  have hdescent : baseEnd_401123 < baseStart_401123 := by decide
  rcases family_descends (prefixWord ++ tailWord_401123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401149 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 2, 1, 7]
def baseStart_401149 : Nat := 118140960795 + 401149 * 2 ^ 59
def prefixEnd_401149 : Nat := 4983230072969 + 3 ^ 40 * 401149 * 2
def baseEnd_401149 : Nat := 205982251070556236392655

theorem tailTrace_401149 : CollatzResearch.WordTrace tailWord_401149 prefixEnd_401149 205982251070556236392655 := by
  unfold tailWord_401149
  simp only [CollatzResearch.WordTrace]
  refine ⟨14631106023713158639886501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9754070682475439093257667 14631106023713158639886501)
  ·
    refine ⟨2743332379446217244978719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14631106023713158639886501 2743332379446217244978719)
    ·
      refine ⟨4114998569169325867468079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2743332379446217244978719 4114998569169325867468079)
      ·
        refine ⟨6172497853753988801202119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4114998569169325867468079 6172497853753988801202119)
        ·
          refine ⟨9258746780630983201803179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6172497853753988801202119 9258746780630983201803179)
          ·
            refine ⟨13888120170946474802704769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9258746780630983201803179 13888120170946474802704769)
            ·
              refine ⟨10416090128209856102028577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13888120170946474802704769 10416090128209856102028577)
              ·
                refine ⟨7812067596157392076521433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10416090128209856102028577 7812067596157392076521433)
                ·
                  refine ⟨5859050697118044057391075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7812067596157392076521433 5859050697118044057391075)
                  ·
                    refine ⟨8788576045677066086086613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5859050697118044057391075 8788576045677066086086613)
                    ·
                      refine ⟨205982251070556236392655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 8788576045677066086086613 205982251070556236392655)
                      ·
                        rfl

theorem cell23_401149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_401149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401149 prefixEnd_401149 := by exact prefixLift 401149
  have htrace : WordTrace (prefixWord ++ tailWord_401149) baseStart_401149 baseEnd_401149 := by
    simpa [prefixWord, tailWord_401149, baseEnd_401149] using wordTrace_append hprefix tailTrace_401149
  have hstable : (prefixWord ++ tailWord_401149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401149).length < 2 ^ (prefixWord ++ tailWord_401149).sum := by decide
  have hdescent : baseEnd_401149 < baseStart_401149 := by decide
  rcases family_descends (prefixWord ++ tailWord_401149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401153 : List Nat := [1, 2, 4, 1, 1, 1, 3, 3, 3, 1, 3]
def baseStart_401153 : Nat := 118140960795 + 401153 * 2 ^ 59
def prefixEnd_401153 : Nat := 4983230072969 + 3 ^ 40 * 401153 * 2
def baseEnd_401153 : Nat := 205984304993174220742637

theorem tailTrace_401153 : CollatzResearch.WordTrace tailWord_401153 prefixEnd_401153 205984304993174220742637 := by
  unfold tailWord_401153
  simp only [CollatzResearch.WordTrace]
  refine ⟨14631251915698667323032113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9754167943799111548688075 14631251915698667323032113)
  ·
    refine ⟨10973438936774000492274085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14631251915698667323032113 10973438936774000492274085)
    ·
      refine ⟨2057519800645125092301391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10973438936774000492274085 2057519800645125092301391)
      ·
        refine ⟨3086279700967687638452087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2057519800645125092301391 3086279700967687638452087)
        ·
          refine ⟨4629419551451531457678131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3086279700967687638452087 4629419551451531457678131)
          ·
            refine ⟨6944129327177297186517197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4629419551451531457678131 6944129327177297186517197)
            ·
              refine ⟨2604048497691486444943949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6944129327177297186517197 2604048497691486444943949)
              ·
                refine ⟨976518186634307416853981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2604048497691486444943949 976518186634307416853981)
                ·
                  refine ⟨366194319987865281320243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 976518186634307416853981 366194319987865281320243)
                  ·
                    refine ⟨549291479981797921980365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 366194319987865281320243 549291479981797921980365)
                    ·
                      refine ⟨205984304993174220742637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 549291479981797921980365 205984304993174220742637)
                      ·
                        rfl

theorem cell23_401153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_401153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401153 prefixEnd_401153 := by exact prefixLift 401153
  have htrace : WordTrace (prefixWord ++ tailWord_401153) baseStart_401153 baseEnd_401153 := by
    simpa [prefixWord, tailWord_401153, baseEnd_401153] using wordTrace_append hprefix tailTrace_401153
  have hstable : (prefixWord ++ tailWord_401153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401153).length < 2 ^ (prefixWord ++ tailWord_401153).sum := by decide
  have hdescent : baseEnd_401153 < baseStart_401153 := by decide
  rcases family_descends (prefixWord ++ tailWord_401153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401173 : List Nat := [1, 3, 2, 1, 2, 4, 2, 2, 1, 5]
def baseStart_401173 : Nat := 118140960795 + 401173 * 2 ^ 59
def prefixEnd_401173 : Nat := 4983230072969 + 3 ^ 40 * 401173 * 2
def baseEnd_401173 : Nat := 68664858202088047497515

theorem tailTrace_401173 : CollatzResearch.WordTrace tailWord_401173 prefixEnd_401173 68664858202088047497515 := by
  unfold tailWord_401173
  simp only [CollatzResearch.WordTrace]
  refine ⟨14631981375626210738760173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9754654250417473825840115 14631981375626210738760173)
  ·
    refine ⟨5486993015859829027035065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14631981375626210738760173 5486993015859829027035065)
    ·
      refine ⟨4115244761894871770276299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5486993015859829027035065 4115244761894871770276299)
      ·
        refine ⟨6172867142842307655414449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4115244761894871770276299 6172867142842307655414449)
        ·
          refine ⟨4629650357131730741560837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6172867142842307655414449 4629650357131730741560837)
          ·
            refine ⟨868059441962199514042657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4629650357131730741560837 868059441962199514042657)
            ·
              refine ⟨651044581471649635531993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 868059441962199514042657 651044581471649635531993)
              ·
                refine ⟨488283436103737226648995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 651044581471649635531993 488283436103737226648995)
                ·
                  refine ⟨732425154155605839973493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 488283436103737226648995 732425154155605839973493)
                  ·
                    refine ⟨68664858202088047497515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 732425154155605839973493 68664858202088047497515)
                    ·
                      rfl

theorem cell23_401173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2, 1, 5].length) (baseStart_401173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401173 prefixEnd_401173 := by exact prefixLift 401173
  have htrace : WordTrace (prefixWord ++ tailWord_401173) baseStart_401173 baseEnd_401173 := by
    simpa [prefixWord, tailWord_401173, baseEnd_401173] using wordTrace_append hprefix tailTrace_401173
  have hstable : (prefixWord ++ tailWord_401173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401173).length < 2 ^ (prefixWord ++ tailWord_401173).sum := by decide
  have hdescent : baseEnd_401173 < baseStart_401173 := by decide
  rcases family_descends (prefixWord ++ tailWord_401173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401176 : List Nat := [2, 1, 2, 3, 1, 1, 2, 3, 3, 1, 4]
def baseStart_401176 : Nat := 118140960795 + 401176 * 2 ^ 59
def prefixEnd_401176 : Nat := 4983230072969 + 3 ^ 40 * 401176 * 2
def baseEnd_401176 : Nat := 205996115048227630755031

theorem tailTrace_401176 : CollatzResearch.WordTrace tailWord_401176 prefixEnd_401176 205996115048227630755031 := by
  unfold tailWord_401176
  simp only [CollatzResearch.WordTrace]
  refine ⟨7316045397307671125559691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9754727196410228167412921 7316045397307671125559691)
  ·
    refine ⟨10974068095961506688339537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7316045397307671125559691 10974068095961506688339537)
    ·
      refine ⟨8230551071971130016254653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10974068095961506688339537 8230551071971130016254653)
      ·
        refine ⟨3086456651989173756095495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8230551071971130016254653 3086456651989173756095495)
        ·
          refine ⟨4629684977983760634143243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3086456651989173756095495 4629684977983760634143243)
          ·
            refine ⟨6944527466975640951214865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4629684977983760634143243 6944527466975640951214865)
            ·
              refine ⟨5208395600231730713411149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6944527466975640951214865 5208395600231730713411149)
              ·
                refine ⟨1953148350086899017529181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5208395600231730713411149 1953148350086899017529181)
                ·
                  refine ⟨732430631282587131573443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1953148350086899017529181 732430631282587131573443)
                  ·
                    refine ⟨1098645946923880697360165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 732430631282587131573443 1098645946923880697360165)
                    ·
                      refine ⟨205996115048227630755031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1098645946923880697360165 205996115048227630755031)
                      ·
                        rfl

theorem cell23_401176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_401176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401176 prefixEnd_401176 := by exact prefixLift 401176
  have htrace : WordTrace (prefixWord ++ tailWord_401176) baseStart_401176 baseEnd_401176 := by
    simpa [prefixWord, tailWord_401176, baseEnd_401176] using wordTrace_append hprefix tailTrace_401176
  have hstable : (prefixWord ++ tailWord_401176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401176).length < 2 ^ (prefixWord ++ tailWord_401176).sum := by decide
  have hdescent : baseEnd_401176 < baseStart_401176 := by decide
  rcases family_descends (prefixWord ++ tailWord_401176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401186 : List Nat := [3, 3, 1, 1, 2, 1, 2, 1, 3, 6]
def baseStart_401186 : Nat := 118140960795 + 401186 * 2 ^ 59
def prefixEnd_401186 : Nat := 4983230072969 + 3 ^ 40 * 401186 * 2
def baseEnd_401186 : Nat := 68667083284924197209995

theorem tailTrace_401186 : CollatzResearch.WordTrace tailWord_401186 prefixEnd_401186 68667083284924197209995 := by
  unfold tailWord_401186
  simp only [CollatzResearch.WordTrace]
  refine ⟨3658113881144778489745853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9754970349719409305988941 3658113881144778489745853)
  ·
    refine ⟨1371792705429291933654695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3658113881144778489745853 1371792705429291933654695)
    ·
      refine ⟨2057689058143937900482043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1371792705429291933654695 2057689058143937900482043)
      ·
        refine ⟨3086533587215906850723065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2057689058143937900482043 3086533587215906850723065)
        ·
          refine ⟨2314900190411930138042299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3086533587215906850723065 2314900190411930138042299)
          ·
            refine ⟨3472350285617895207063449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2314900190411930138042299 3472350285617895207063449)
            ·
              refine ⟨2604262714213421405297587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3472350285617895207063449 2604262714213421405297587)
              ·
                refine ⟨3906394071320132107946381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2604262714213421405297587 3906394071320132107946381)
                ·
                  refine ⟨1464897776745049540479893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3906394071320132107946381 1464897776745049540479893)
                  ·
                    refine ⟨68667083284924197209995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1464897776745049540479893 68667083284924197209995)
                    ·
                      rfl

theorem cell23_401186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_401186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401186 prefixEnd_401186 := by exact prefixLift 401186
  have htrace : WordTrace (prefixWord ++ tailWord_401186) baseStart_401186 baseEnd_401186 := by
    simpa [prefixWord, tailWord_401186, baseEnd_401186] using wordTrace_append hprefix tailTrace_401186
  have hstable : (prefixWord ++ tailWord_401186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401186).length < 2 ^ (prefixWord ++ tailWord_401186).sum := by decide
  have hdescent : baseEnd_401186 < baseStart_401186 := by decide
  rcases family_descends (prefixWord ++ tailWord_401186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401196 : List Nat := [2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 5]
def baseStart_401196 : Nat := 118140960795 + 401196 * 2 ^ 59
def prefixEnd_401196 : Nat := 4983230072969 + 3 ^ 40 * 401196 * 2
def baseEnd_401196 : Nat := 206006384661317552504939

theorem tailTrace_401196 : CollatzResearch.WordTrace tailWord_401196 prefixEnd_401196 206006384661317552504939 := by
  unfold tailWord_401196
  simp only [CollatzResearch.WordTrace]
  refine ⟨7316410127271442833423721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9755213503028590444564961 7316410127271442833423721)
  ·
    refine ⟨5487307595453582125067791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7316410127271442833423721 5487307595453582125067791)
    ·
      refine ⟨8230961393180373187601687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5487307595453582125067791 8230961393180373187601687)
      ·
        refine ⟨12346442089770559781402531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8230961393180373187601687 12346442089770559781402531)
        ·
          refine ⟨18519663134655839672103797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12346442089770559781402531 18519663134655839672103797)
          ·
            refine ⟨1736218418873984969259731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18519663134655839672103797 1736218418873984969259731)
            ·
              refine ⟨2604327628310977453889597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1736218418873984969259731 2604327628310977453889597)
              ·
                refine ⟨976622860616616545208599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2604327628310977453889597 976622860616616545208599)
                ·
                  refine ⟨1464934290924924817812899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 976622860616616545208599 1464934290924924817812899)
                  ·
                    refine ⟨2197401436387387226719349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1464934290924924817812899 2197401436387387226719349)
                    ·
                      refine ⟨206006384661317552504939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2197401436387387226719349 206006384661317552504939)
                      ·
                        rfl

theorem cell23_401196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 5].length) (baseStart_401196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401196 prefixEnd_401196 := by exact prefixLift 401196
  have htrace : WordTrace (prefixWord ++ tailWord_401196) baseStart_401196 baseEnd_401196 := by
    simpa [prefixWord, tailWord_401196, baseEnd_401196] using wordTrace_append hprefix tailTrace_401196
  have hstable : (prefixWord ++ tailWord_401196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401196).length < 2 ^ (prefixWord ++ tailWord_401196).sum := by decide
  have hdescent : baseEnd_401196 < baseStart_401196 := by decide
  rcases family_descends (prefixWord ++ tailWord_401196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401213 : List Nat := [1, 4, 1, 4, 1, 1, 2, 2, 1, 1, 5]
def baseStart_401213 : Nat := 118140960795 + 401213 * 2 ^ 59
def prefixEnd_401213 : Nat := 4983230072969 + 3 ^ 40 * 401213 * 2
def baseEnd_401213 : Nat := 206015113832443985992361

theorem tailTrace_401213 : CollatzResearch.WordTrace tailWord_401213 prefixEnd_401213 206015113832443985992361 := by
  unfold tailWord_401213
  simp only [CollatzResearch.WordTrace]
  refine ⟨14633440295481297570216293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9755626863654198380144195 14633440295481297570216293)
  ·
    refine ⟨2743770055402743294415555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14633440295481297570216293 2743770055402743294415555)
    ·
      refine ⟨4115655083104114941623333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2743770055402743294415555 4115655083104114941623333)
      ·
        refine ⟨771685328082021551554375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4115655083104114941623333 771685328082021551554375)
        ·
          refine ⟨1157527992123032327331563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 771685328082021551554375 1157527992123032327331563)
          ·
            refine ⟨1736291988184548490997345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1157527992123032327331563 1736291988184548490997345)
            ·
              refine ⟨1302218991138411368248009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1736291988184548490997345 1302218991138411368248009)
              ·
                refine ⟨976664243353808526186007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1302218991138411368248009 976664243353808526186007)
                ·
                  refine ⟨1464996365030712789279011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 976664243353808526186007 1464996365030712789279011)
                  ·
                    refine ⟨2197494547546069183918517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1464996365030712789279011 2197494547546069183918517)
                    ·
                      refine ⟨206015113832443985992361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2197494547546069183918517 206015113832443985992361)
                      ·
                        rfl

theorem cell23_401213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_401213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401213 prefixEnd_401213 := by exact prefixLift 401213
  have htrace : WordTrace (prefixWord ++ tailWord_401213) baseStart_401213 baseEnd_401213 := by
    simpa [prefixWord, tailWord_401213, baseEnd_401213] using wordTrace_append hprefix tailTrace_401213
  have hstable : (prefixWord ++ tailWord_401213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401213).length < 2 ^ (prefixWord ++ tailWord_401213).sum := by decide
  have hdescent : baseEnd_401213 < baseStart_401213 := by decide
  rcases family_descends (prefixWord ++ tailWord_401213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401260 : List Nat := [2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 3]
def baseStart_401260 : Nat := 118140960795 + 401260 * 2 ^ 59
def prefixEnd_401260 : Nat := 4983230072969 + 3 ^ 40 * 401260 * 2
def baseEnd_401260 : Nat := 206039247423205302104645

theorem tailTrace_401260 : CollatzResearch.WordTrace tailWord_401260 prefixEnd_401260 206039247423205302104645 := by
  unfold tailWord_401260
  simp only [CollatzResearch.WordTrace]
  refine ⟨7317577263155512298588617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9756769684207349731451489 7317577263155512298588617)
  ·
    refine ⟨5488182947366634223941463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7317577263155512298588617 5488182947366634223941463)
    ·
      refine ⟨8232274421049951335912195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5488182947366634223941463 8232274421049951335912195)
      ·
        refine ⟨12348411631574927003868293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8232274421049951335912195 12348411631574927003868293)
        ·
          refine ⟨2315327180920298813225305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12348411631574927003868293 2315327180920298813225305)
          ·
            refine ⟨1736495385690224109918979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2315327180920298813225305 1736495385690224109918979)
            ·
              refine ⟨2604743078535336164878469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1736495385690224109918979 2604743078535336164878469)
              ·
                refine ⟨488389327225375530914713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2604743078535336164878469 488389327225375530914713)
                ·
                  refine ⟨366291995419031648186035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 488389327225375530914713 366291995419031648186035)
                  ·
                    refine ⟨549437993128547472279053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 366291995419031648186035 549437993128547472279053)
                    ·
                      refine ⟨206039247423205302104645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 549437993128547472279053 206039247423205302104645)
                      ·
                        rfl

theorem cell23_401260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 3].length) (baseStart_401260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401260 prefixEnd_401260 := by exact prefixLift 401260
  have htrace : WordTrace (prefixWord ++ tailWord_401260) baseStart_401260 baseEnd_401260 := by
    simpa [prefixWord, tailWord_401260, baseEnd_401260] using wordTrace_append hprefix tailTrace_401260
  have hstable : (prefixWord ++ tailWord_401260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401260).length < 2 ^ (prefixWord ++ tailWord_401260).sum := by decide
  have hdescent : baseEnd_401260 < baseStart_401260 := by decide
  rcases family_descends (prefixWord ++ tailWord_401260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401296 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 4]
def baseStart_401296 : Nat := 118140960795 + 401296 * 2 ^ 59
def prefixEnd_401296 : Nat := 4983230072969 + 3 ^ 40 * 401296 * 2
def baseEnd_401296 : Nat := 206057732726767161254479

theorem tailTrace_401296 : CollatzResearch.WordTrace tailWord_401296 prefixEnd_401296 206057732726767161254479 := by
  unfold tailWord_401296
  simp only [CollatzResearch.WordTrace]
  refine ⟨7318233777090301372743871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9757645036120401830325161 7318233777090301372743871)
  ·
    refine ⟨10977350665635452059115807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7318233777090301372743871 10977350665635452059115807)
    ·
      refine ⟨16466025998453178088673711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10977350665635452059115807 16466025998453178088673711)
      ·
        refine ⟨24699038997679767133010567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16466025998453178088673711 24699038997679767133010567)
        ·
          refine ⟨37048558496519650699515851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24699038997679767133010567 37048558496519650699515851)
          ·
            refine ⟨55572837744779476049273777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37048558496519650699515851 55572837744779476049273777)
            ·
              refine ⟨41679628308584607036955333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55572837744779476049273777 41679628308584607036955333)
              ·
                refine ⟨7814930307859613819429125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41679628308584607036955333 7814930307859613819429125)
                ·
                  refine ⟨1465299432723677591142961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7814930307859613819429125 1465299432723677591142961)
                  ·
                    refine ⟨1098974574542758193357221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1465299432723677591142961 1098974574542758193357221)
                    ·
                      refine ⟨206057732726767161254479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1098974574542758193357221 206057732726767161254479)
                      ·
                        rfl

theorem cell23_401296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 4].length) (baseStart_401296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401296 prefixEnd_401296 := by exact prefixLift 401296
  have htrace : WordTrace (prefixWord ++ tailWord_401296) baseStart_401296 baseEnd_401296 := by
    simpa [prefixWord, tailWord_401296, baseEnd_401296] using wordTrace_append hprefix tailTrace_401296
  have hstable : (prefixWord ++ tailWord_401296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401296).length < 2 ^ (prefixWord ++ tailWord_401296).sum := by decide
  have hdescent : baseEnd_401296 < baseStart_401296 := by decide
  rcases family_descends (prefixWord ++ tailWord_401296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401304 : List Nat := [2, 1, 2, 6, 1, 1, 1, 3, 1, 3, 2]
def baseStart_401304 : Nat := 118140960795 + 401304 * 2 ^ 59
def prefixEnd_401304 : Nat := 4983230072969 + 3 ^ 40 * 401304 * 2
def baseEnd_401304 : Nat := 206061840572003129954443

theorem tailTrace_401304 : CollatzResearch.WordTrace tailWord_401304 prefixEnd_401304 206061840572003129954443 := by
  unfold tailWord_401304
  simp only [CollatzResearch.WordTrace]
  refine ⟨7318379669075810055889483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9757839558767746741185977 7318379669075810055889483)
  ·
    refine ⟨10977569503613715083834225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7318379669075810055889483 10977569503613715083834225)
    ·
      refine ⟨8233177127710286312875669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10977569503613715083834225 8233177127710286312875669)
      ·
        refine ⟨385930177861419670916047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8233177127710286312875669 385930177861419670916047)
        ·
          refine ⟨578895266792129506374071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385930177861419670916047 578895266792129506374071)
          ·
            refine ⟨868342900188194259561107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 578895266792129506374071 868342900188194259561107)
            ·
              refine ⟨1302514350282291389341661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 868342900188194259561107 1302514350282291389341661)
              ·
                refine ⟨488442881355859271003123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1302514350282291389341661 488442881355859271003123)
                ·
                  refine ⟨732664322033788906504685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 488442881355859271003123 732664322033788906504685)
                  ·
                    refine ⟨274749120762670839939257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 732664322033788906504685 274749120762670839939257)
                    ·
                      refine ⟨206061840572003129954443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 274749120762670839939257 206061840572003129954443)
                      ·
                        rfl

theorem cell23_401304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_401304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401304 prefixEnd_401304 := by exact prefixLift 401304
  have htrace : WordTrace (prefixWord ++ tailWord_401304) baseStart_401304 baseEnd_401304 := by
    simpa [prefixWord, tailWord_401304, baseEnd_401304] using wordTrace_append hprefix tailTrace_401304
  have hstable : (prefixWord ++ tailWord_401304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401304).length < 2 ^ (prefixWord ++ tailWord_401304).sum := by decide
  have hdescent : baseEnd_401304 < baseStart_401304 := by decide
  rcases family_descends (prefixWord ++ tailWord_401304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401336 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 3, 7]
def baseStart_401336 : Nat := 118140960795 + 401336 * 2 ^ 59
def prefixEnd_401336 : Nat := 4983230072969 + 3 ^ 40 * 401336 * 2
def baseEnd_401336 : Nat := 68692757317649001584765

theorem tailTrace_401336 : CollatzResearch.WordTrace tailWord_401336 prefixEnd_401336 68692757317649001584765 := by
  unfold tailWord_401336
  simp only [CollatzResearch.WordTrace]
  refine ⟨7318963237017844788471931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9758617649357126384629241 7318963237017844788471931)
  ·
    refine ⟨10978444855526767182707897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7318963237017844788471931 10978444855526767182707897)
    ·
      refine ⟨8233833641645075387030923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10978444855526767182707897 8233833641645075387030923)
      ·
        refine ⟨12350750462467613080546385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8233833641645075387030923 12350750462467613080546385)
        ·
          refine ⟨9263062846850709810409789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12350750462467613080546385 9263062846850709810409789)
          ·
            refine ⟨3473648567569016178903671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9263062846850709810409789 3473648567569016178903671)
            ·
              refine ⟨5210472851353524268355507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3473648567569016178903671 5210472851353524268355507)
              ·
                refine ⟨7815709277030286402533261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5210472851353524268355507 7815709277030286402533261)
                ·
                  refine ⟨2930890978886357400949973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7815709277030286402533261 2930890978886357400949973)
                  ·
                    refine ⟨68692757317649001584765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2930890978886357400949973 68692757317649001584765)
                    ·
                      rfl

theorem cell23_401336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 3, 7].length) (baseStart_401336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401336 prefixEnd_401336 := by exact prefixLift 401336
  have htrace : WordTrace (prefixWord ++ tailWord_401336) baseStart_401336 baseEnd_401336 := by
    simpa [prefixWord, tailWord_401336, baseEnd_401336] using wordTrace_append hprefix tailTrace_401336
  have hstable : (prefixWord ++ tailWord_401336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401336).length < 2 ^ (prefixWord ++ tailWord_401336).sum := by decide
  have hdescent : baseEnd_401336 < baseStart_401336 := by decide
  rcases family_descends (prefixWord ++ tailWord_401336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401370 : List Nat := [3, 1, 1, 2, 5, 1, 1, 2, 2, 5]
def baseStart_401370 : Nat := 118140960795 + 401370 * 2 ^ 59
def prefixEnd_401370 : Nat := 4983230072969 + 3 ^ 40 * 401370 * 2
def baseEnd_401370 : Nat := 68698576765066623909713

theorem tailTrace_401370 : CollatzResearch.WordTrace tailWord_401370 prefixEnd_401370 68698576765066623909713 := by
  unfold tailWord_401370
  simp only [CollatzResearch.WordTrace]
  refine ⟨3659791638978128345920391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9759444370608342255787709 3659791638978128345920391)
  ·
    refine ⟨5489687458467192518880587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3659791638978128345920391 5489687458467192518880587)
    ·
      refine ⟨8234531187700788778320881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5489687458467192518880587 8234531187700788778320881)
      ·
        refine ⟨6175898390775591583740661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8234531187700788778320881 6175898390775591583740661)
        ·
          refine ⟨578990474135211710975687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6175898390775591583740661 578990474135211710975687)
          ·
            refine ⟨868485711202817566463531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 578990474135211710975687 868485711202817566463531)
            ·
              refine ⟨1302728566804226349695297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 868485711202817566463531 1302728566804226349695297)
              ·
                refine ⟨977046425103169762271473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1302728566804226349695297 977046425103169762271473)
                ·
                  refine ⟨732784818827377321703605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 977046425103169762271473 732784818827377321703605)
                  ·
                    refine ⟨68698576765066623909713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 732784818827377321703605 68698576765066623909713)
                    ·
                      rfl

theorem cell23_401370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 2, 5].length) (baseStart_401370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401370 prefixEnd_401370 := by exact prefixLift 401370
  have htrace : WordTrace (prefixWord ++ tailWord_401370) baseStart_401370 baseEnd_401370 := by
    simpa [prefixWord, tailWord_401370, baseEnd_401370] using wordTrace_append hprefix tailTrace_401370
  have hstable : (prefixWord ++ tailWord_401370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401370).length < 2 ^ (prefixWord ++ tailWord_401370).sum := by decide
  have hdescent : baseEnd_401370 < baseStart_401370 := by decide
  rcases family_descends (prefixWord ++ tailWord_401370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401434 : List Nat := [3, 1, 1, 3, 1, 3, 4, 2, 1, 4]
def baseStart_401434 : Nat := 118140960795 + 401434 * 2 ^ 59
def prefixEnd_401434 : Nat := 4983230072969 + 3 ^ 40 * 401434 * 2
def baseEnd_401434 : Nat := 68709531019029207109615

theorem tailTrace_401434 : CollatzResearch.WordTrace tailWord_401434 prefixEnd_401434 68709531019029207109615 := by
  unfold tailWord_401434
  simp only [CollatzResearch.WordTrace]
  refine ⟨3660375206920163078502839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9761000551787101542674237 3660375206920163078502839)
  ·
    refine ⟨5490562810380244617754259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3660375206920163078502839 5490562810380244617754259)
    ·
      refine ⟨8235844215570366926631389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5490562810380244617754259 8235844215570366926631389)
      ·
        refine ⟨3088441580838887597486771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8235844215570366926631389 3088441580838887597486771)
        ·
          refine ⟨4632662371258331396230157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3088441580838887597486771 4632662371258331396230157)
          ·
            refine ⟨1737248389221874273586309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4632662371258331396230157 1737248389221874273586309)
            ·
              refine ⟨325734072979101426297433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1737248389221874273586309 325734072979101426297433)
              ·
                refine ⟨244300554734326069723075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 325734072979101426297433 244300554734326069723075)
                ·
                  refine ⟨366450832101489104584613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 244300554734326069723075 366450832101489104584613)
                  ·
                    refine ⟨68709531019029207109615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 366450832101489104584613 68709531019029207109615)
                    ·
                      rfl

theorem cell23_401434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 2, 1, 4].length) (baseStart_401434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401434 prefixEnd_401434 := by exact prefixLift 401434
  have htrace : WordTrace (prefixWord ++ tailWord_401434) baseStart_401434 baseEnd_401434 := by
    simpa [prefixWord, tailWord_401434, baseEnd_401434] using wordTrace_append hprefix tailTrace_401434
  have hstable : (prefixWord ++ tailWord_401434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401434).length < 2 ^ (prefixWord ++ tailWord_401434).sum := by decide
  have hdescent : baseEnd_401434 < baseStart_401434 := by decide
  rcases family_descends (prefixWord ++ tailWord_401434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401443 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 5, 5]
def baseStart_401443 : Nat := 118140960795 + 401443 * 2 ^ 59
def prefixEnd_401443 : Nat := 4983230072969 + 3 ^ 40 * 401443 * 2
def baseEnd_401443 : Nat := 68711071460992695372101

theorem tailTrace_401443 : CollatzResearch.WordTrace tailWord_401443 prefixEnd_401443 68711071460992695372101 := by
  unfold tailWord_401443
  simp only [CollatzResearch.WordTrace]
  refine ⟨14641829084648046851088983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9761219389765364567392655 14641829084648046851088983)
  ·
    refine ⟨21962743626972070276633475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14641829084648046851088983 21962743626972070276633475)
    ·
      refine ⟨32944115440458105414950213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21962743626972070276633475 32944115440458105414950213)
      ·
        refine ⟨6177021645085894765303165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32944115440458105414950213 6177021645085894765303165)
        ·
          refine ⟨2316383116907210536988687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6177021645085894765303165 2316383116907210536988687)
          ·
            refine ⟨3474574675360815805483031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2316383116907210536988687 3474574675360815805483031)
            ·
              refine ⟨5211862013041223708224547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3474574675360815805483031 5211862013041223708224547)
              ·
                refine ⟨7817793019561835562336821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5211862013041223708224547 7817793019561835562336821)
                ·
                  refine ⟨732918095583922083969077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7817793019561835562336821 732918095583922083969077)
                  ·
                    refine ⟨68711071460992695372101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 732918095583922083969077 68711071460992695372101)
                    ·
                      rfl

theorem cell23_401443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5, 5].length) (baseStart_401443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401443 prefixEnd_401443 := by exact prefixLift 401443
  have htrace : WordTrace (prefixWord ++ tailWord_401443) baseStart_401443 baseEnd_401443 := by
    simpa [prefixWord, tailWord_401443, baseEnd_401443] using wordTrace_append hprefix tailTrace_401443
  have hstable : (prefixWord ++ tailWord_401443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401443).length < 2 ^ (prefixWord ++ tailWord_401443).sum := by decide
  have hdescent : baseEnd_401443 < baseStart_401443 := by decide
  rcases family_descends (prefixWord ++ tailWord_401443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401457 : List Nat := [1, 2, 2, 3, 1, 4, 1, 2, 3, 1, 3]
def baseStart_401457 : Nat := 118140960795 + 401457 * 2 ^ 59
def prefixEnd_401457 : Nat := 4983230072969 + 3 ^ 40 * 401457 * 2
def baseEnd_401457 : Nat := 206140403112141031341239

theorem tailTrace_401457 : CollatzResearch.WordTrace tailWord_401457 prefixEnd_401457 206140403112141031341239 := by
  unfold tailWord_401457
  simp only [CollatzResearch.WordTrace]
  refine ⟨14642339706597327242098625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9761559804398218161399083 14642339706597327242098625)
  ·
    refine ⟨10981754779947995431573969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14642339706597327242098625 10981754779947995431573969)
    ·
      refine ⟨8236316084960996573680477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10981754779947995431573969 8236316084960996573680477)
      ·
        refine ⟨3088618531860373715130179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8236316084960996573680477 3088618531860373715130179)
        ·
          refine ⟨4632927797790560572695269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3088618531860373715130179 4632927797790560572695269)
          ·
            refine ⟨868673962085730107380363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4632927797790560572695269 868673962085730107380363)
            ·
              refine ⟨1303010943128595161070545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 868673962085730107380363 1303010943128595161070545)
              ·
                refine ⟨977258207346446370802909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1303010943128595161070545 977258207346446370802909)
                ·
                  refine ⟨366471827754917389051091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 977258207346446370802909 366471827754917389051091)
                  ·
                    refine ⟨549707741632376083576637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 366471827754917389051091 549707741632376083576637)
                    ·
                      refine ⟨206140403112141031341239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 549707741632376083576637 206140403112141031341239)
                      ·
                        rfl

theorem cell23_401457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_401457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401457 prefixEnd_401457 := by exact prefixLift 401457
  have htrace : WordTrace (prefixWord ++ tailWord_401457) baseStart_401457 baseEnd_401457 := by
    simpa [prefixWord, tailWord_401457, baseEnd_401457] using wordTrace_append hprefix tailTrace_401457
  have hstable : (prefixWord ++ tailWord_401457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401457).length < 2 ^ (prefixWord ++ tailWord_401457).sum := by decide
  have hdescent : baseEnd_401457 < baseStart_401457 := by decide
  rcases family_descends (prefixWord ++ tailWord_401457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401500 : List Nat := [2, 2, 4, 1, 1, 2, 1, 1, 3, 1, 5]
def baseStart_401500 : Nat := 118140960795 + 401500 * 2 ^ 59
def prefixEnd_401500 : Nat := 4983230072969 + 3 ^ 40 * 401500 * 2
def baseEnd_401500 : Nat := 206162482780284363103541

theorem tailTrace_401500 : CollatzResearch.WordTrace tailWord_401500 prefixEnd_401500 206162482780284363103541 := by
  unfold tailWord_401500
  simp only [CollatzResearch.WordTrace]
  refine ⟨7321954022720772792956977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9762605363627697057275969 7321954022720772792956977)
  ·
    refine ⟨5491465517040579594717733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7321954022720772792956977 5491465517040579594717733)
    ·
      refine ⟨1029649784445108674009575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5491465517040579594717733 1029649784445108674009575)
      ·
        refine ⟨1544474676667663011014363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1029649784445108674009575 1544474676667663011014363)
        ·
          refine ⟨2316712015001494516521545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1544474676667663011014363 2316712015001494516521545)
          ·
            refine ⟨1737534011251120887391159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2316712015001494516521545 1737534011251120887391159)
            ·
              refine ⟨2606301016876681331086739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1737534011251120887391159 2606301016876681331086739)
              ·
                refine ⟨3909451525315021996630109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2606301016876681331086739 3909451525315021996630109)
                ·
                  refine ⟨1466044321993133248736291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3909451525315021996630109 1466044321993133248736291)
                  ·
                    refine ⟨2199066482989699873104437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1466044321993133248736291 2199066482989699873104437)
                    ·
                      refine ⟨206162482780284363103541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2199066482989699873104437 206162482780284363103541)
                      ·
                        rfl

theorem cell23_401500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_401500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401500 prefixEnd_401500 := by exact prefixLift 401500
  have htrace : WordTrace (prefixWord ++ tailWord_401500) baseStart_401500 baseEnd_401500 := by
    simpa [prefixWord, tailWord_401500, baseEnd_401500] using wordTrace_append hprefix tailTrace_401500
  have hstable : (prefixWord ++ tailWord_401500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401500).length < 2 ^ (prefixWord ++ tailWord_401500).sum := by decide
  have hdescent : baseEnd_401500 < baseStart_401500 := by decide
  rcases family_descends (prefixWord ++ tailWord_401500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401514 : List Nat := [3, 1, 3, 2, 3, 1, 2, 2, 1, 1, 4]
def baseStart_401514 : Nat := 118140960795 + 401514 * 2 ^ 59
def prefixEnd_401514 : Nat := 4983230072969 + 3 ^ 40 * 401514 * 2
def baseEnd_401514 : Nat := 206169671509447308328477

theorem tailTrace_401514 : CollatzResearch.WordTrace tailWord_401514 prefixEnd_401514 206169671509447308328477 := by
  unfold tailWord_401514
  simp only [CollatzResearch.WordTrace]
  refine ⟨3661104666847706494230899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9762945778260550651282397 3661104666847706494230899)
  ·
    refine ⟨5491657000271559741346349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3661104666847706494230899 5491657000271559741346349)
    ·
      refine ⟨2059371375101834903004881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5491657000271559741346349 2059371375101834903004881)
      ·
        refine ⟨1544528531326376177253661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2059371375101834903004881 1544528531326376177253661)
        ·
          refine ⟨579198199247391066470123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1544528531326376177253661 579198199247391066470123)
          ·
            refine ⟨868797298871086599705185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 579198199247391066470123 868797298871086599705185)
            ·
              refine ⟨651597974153314949778889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 868797298871086599705185 651597974153314949778889)
              ·
                refine ⟨488698480614986212334167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 651597974153314949778889 488698480614986212334167)
                ·
                  refine ⟨733047720922479318501251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 488698480614986212334167 733047720922479318501251)
                  ·
                    refine ⟨1099571581383718977751877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 733047720922479318501251 1099571581383718977751877)
                    ·
                      refine ⟨206169671509447308328477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1099571581383718977751877 206169671509447308328477)
                      ·
                        rfl

theorem cell23_401514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_401514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401514 prefixEnd_401514 := by exact prefixLift 401514
  have htrace : WordTrace (prefixWord ++ tailWord_401514) baseStart_401514 baseEnd_401514 := by
    simpa [prefixWord, tailWord_401514, baseEnd_401514] using wordTrace_append hprefix tailTrace_401514
  have hstable : (prefixWord ++ tailWord_401514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401514).length < 2 ^ (prefixWord ++ tailWord_401514).sum := by decide
  have hdescent : baseEnd_401514 < baseStart_401514 := by decide
  rcases family_descends (prefixWord ++ tailWord_401514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401520 : List Nat := [2, 1, 1, 1, 5, 2, 4, 7]
def baseStart_401520 : Nat := 118140960795 + 401520 * 2 ^ 59
def prefixEnd_401520 : Nat := 4983230072969 + 3 ^ 40 * 401520 * 2
def baseEnd_401520 : Nat := 7636027866421269809387

theorem tailTrace_401520 : CollatzResearch.WordTrace tailWord_401520 prefixEnd_401520 7636027866421269809387 := by
  unfold tailWord_401520
  simp only [CollatzResearch.WordTrace]
  refine ⟨7322318752684544500821007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9763091670246059334428009 7322318752684544500821007)
  ·
    refine ⟨10983478129026816751231511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7322318752684544500821007 10983478129026816751231511)
    ·
      refine ⟨16475217193540225126847267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10983478129026816751231511 16475217193540225126847267)
      ·
        refine ⟨24712825790310337690270901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16475217193540225126847267 24712825790310337690270901)
        ·
          refine ⟨2316827417841594158462897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24712825790310337690270901 2316827417841594158462897)
          ·
            refine ⟨1737620563381195618847173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2316827417841594158462897 1737620563381195618847173)
            ·
              refine ⟨325803855633974178533845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1737620563381195618847173 325803855633974178533845)
              ·
                refine ⟨7636027866421269809387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 325803855633974178533845 7636027866421269809387)
                ·
                  rfl

theorem cell23_401520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 7].length) (baseStart_401520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401520 prefixEnd_401520 := by exact prefixLift 401520
  have htrace : WordTrace (prefixWord ++ tailWord_401520) baseStart_401520 baseEnd_401520 := by
    simpa [prefixWord, tailWord_401520, baseEnd_401520] using wordTrace_append hprefix tailTrace_401520
  have hstable : (prefixWord ++ tailWord_401520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401520).length < 2 ^ (prefixWord ++ tailWord_401520).sum := by decide
  have hdescent : baseEnd_401520 < baseStart_401520 := by decide
  rcases family_descends (prefixWord ++ tailWord_401520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401537 : List Nat := [1, 2, 4, 2, 4, 1, 9]
def baseStart_401537 : Nat := 118140960795 + 401537 * 2 ^ 59
def prefixEnd_401537 : Nat := 4983230072969 + 3 ^ 40 * 401537 * 2
def baseEnd_401537 : Nat := 2545450389685194053591

theorem tailTrace_401537 : CollatzResearch.WordTrace tailWord_401537 prefixEnd_401537 2545450389685194053591 := by
  unfold tailWord_401537
  simp only [CollatzResearch.WordTrace]
  refine ⟨14645257546307500905010865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9763505030871667270007243 14645257546307500905010865)
  ·
    refine ⟨10983943159730625678758149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14645257546307500905010865 10983943159730625678758149)
    ·
      refine ⟨2059489342449492314767153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10983943159730625678758149 2059489342449492314767153)
      ·
        refine ⟨1544617006837119236075365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2059489342449492314767153 1544617006837119236075365)
        ·
          refine ⟨289615688781959856764131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1544617006837119236075365 289615688781959856764131)
          ·
            refine ⟨434423533172939785146197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289615688781959856764131 434423533172939785146197)
            ·
              refine ⟨2545450389685194053591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 434423533172939785146197 2545450389685194053591)
              ·
                rfl

theorem cell23_401537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 9].length) (baseStart_401537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401537 prefixEnd_401537 := by exact prefixLift 401537
  have htrace : WordTrace (prefixWord ++ tailWord_401537) baseStart_401537 baseEnd_401537 := by
    simpa [prefixWord, tailWord_401537, baseEnd_401537] using wordTrace_append hprefix tailTrace_401537
  have hstable : (prefixWord ++ tailWord_401537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401537).length < 2 ^ (prefixWord ++ tailWord_401537).sum := by decide
  have hdescent : baseEnd_401537 < baseStart_401537 := by decide
  rcases family_descends (prefixWord ++ tailWord_401537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401557 : List Nat := [1, 3, 2, 1, 1, 1, 4, 2, 3, 3, 2]
def baseStart_401557 : Nat := 118140960795 + 401557 * 2 ^ 59
def prefixEnd_401557 : Nat := 4983230072969 + 3 ^ 40 * 401557 * 2
def baseEnd_401557 : Nat := 206191751177590640090779

theorem tailTrace_401557 : CollatzResearch.WordTrace tailWord_401557 prefixEnd_401557 206191751177590640090779 := by
  unfold tailWord_401557
  simp only [CollatzResearch.WordTrace]
  refine ⟨14645987006235044320738925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9763991337490029547159283 14645987006235044320738925)
  ·
    refine ⟨5492245127338141620277097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14645987006235044320738925 5492245127338141620277097)
    ·
      refine ⟨4119183845503606215207823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5492245127338141620277097 4119183845503606215207823)
      ·
        refine ⟨6178775768255409322811735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4119183845503606215207823 6178775768255409322811735)
        ·
          refine ⟨9268163652383113984217603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6178775768255409322811735 9268163652383113984217603)
          ·
            refine ⟨13902245478574670976326405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9268163652383113984217603 13902245478574670976326405)
            ·
              refine ⟨2606671027232750808061201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13902245478574670976326405 2606671027232750808061201)
              ·
                refine ⟨1955003270424563106045901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2606671027232750808061201 1955003270424563106045901)
                ·
                  refine ⟨733126226409211164767213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1955003270424563106045901 733126226409211164767213)
                  ·
                    refine ⟨274922334903454186787705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 733126226409211164767213 274922334903454186787705)
                    ·
                      refine ⟨206191751177590640090779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 274922334903454186787705 206191751177590640090779)
                      ·
                        rfl

theorem cell23_401557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3, 3, 2].length) (baseStart_401557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401557 prefixEnd_401557 := by exact prefixLift 401557
  have htrace : WordTrace (prefixWord ++ tailWord_401557) baseStart_401557 baseEnd_401557 := by
    simpa [prefixWord, tailWord_401557, baseEnd_401557] using wordTrace_append hprefix tailTrace_401557
  have hstable : (prefixWord ++ tailWord_401557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401557).length < 2 ^ (prefixWord ++ tailWord_401557).sum := by decide
  have hdescent : baseEnd_401557 < baseStart_401557 := by decide
  rcases family_descends (prefixWord ++ tailWord_401557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401564 : List Nat := [2, 2, 3, 2, 1, 1, 3, 3, 2, 1, 3]
def baseStart_401564 : Nat := 118140960795 + 401564 * 2 ^ 59
def prefixEnd_401564 : Nat := 4983230072969 + 3 ^ 40 * 401564 * 2
def baseEnd_401564 : Nat := 206195345542172112703247

theorem tailTrace_401564 : CollatzResearch.WordTrace tailWord_401564 prefixEnd_401564 206195345542172112703247 := by
  unfold tailWord_401564
  simp only [CollatzResearch.WordTrace]
  refine ⟨7323121158604842258121873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9764161544806456344162497 7323121158604842258121873)
  ·
    refine ⟨5492340868953631693591405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7323121158604842258121873 5492340868953631693591405)
    ·
      refine ⟨2059627825857611885096777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5492340868953631693591405 2059627825857611885096777)
      ·
        refine ⟨1544720869393208913822583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2059627825857611885096777 1544720869393208913822583)
        ·
          refine ⟨2317081304089813370733875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1544720869393208913822583 2317081304089813370733875)
          ·
            refine ⟨3475621956134720056100813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2317081304089813370733875 3475621956134720056100813)
            ·
              refine ⟨1303358233550520021037805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3475621956134720056100813 1303358233550520021037805)
              ·
                refine ⟨488759337581445007889177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1303358233550520021037805 488759337581445007889177)
                ·
                  refine ⟨366569503186083755916883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 488759337581445007889177 366569503186083755916883)
                  ·
                    refine ⟨549854254779125633875325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 366569503186083755916883 549854254779125633875325)
                    ·
                      refine ⟨206195345542172112703247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 549854254779125633875325 206195345542172112703247)
                      ·
                        rfl

theorem cell23_401564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_401564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401564 prefixEnd_401564 := by exact prefixLift 401564
  have htrace : WordTrace (prefixWord ++ tailWord_401564) baseStart_401564 baseEnd_401564 := by
    simpa [prefixWord, tailWord_401564, baseEnd_401564] using wordTrace_append hprefix tailTrace_401564
  have hstable : (prefixWord ++ tailWord_401564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401564).length < 2 ^ (prefixWord ++ tailWord_401564).sum := by decide
  have hdescent : baseEnd_401564 < baseStart_401564 := by decide
  rcases family_descends (prefixWord ++ tailWord_401564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401591 : List Nat := [1, 1, 3, 1, 4, 3, 3, 1, 1, 3, 2]
def baseStart_401591 : Nat := 118140960795 + 401591 * 2 ^ 59
def prefixEnd_401591 : Nat := 4983230072969 + 3 ^ 40 * 401591 * 2
def baseEnd_401591 : Nat := 206209209519843507065623

theorem tailTrace_401591 : CollatzResearch.WordTrace tailWord_401591 prefixEnd_401591 206209209519843507065623 := by
  unfold tailWord_401591
  simp only [CollatzResearch.WordTrace]
  refine ⟨14647227088111868127476627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9764818058741245418317751 14647227088111868127476627)
  ·
    refine ⟨21970840632167802191214941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14647227088111868127476627 21970840632167802191214941)
    ·
      refine ⟨8239065237062925821705603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21970840632167802191214941 8239065237062925821705603)
      ·
        refine ⟨12358597855594388732558405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8239065237062925821705603 12358597855594388732558405)
        ·
          refine ⟨2317237097923947887354701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12358597855594388732558405 2317237097923947887354701)
          ·
            refine ⟨868963911721480457758013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2317237097923947887354701 868963911721480457758013)
            ·
              refine ⟨325861466895555171659255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 868963911721480457758013 325861466895555171659255)
              ·
                refine ⟨488792200343332757488883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 325861466895555171659255 488792200343332757488883)
                ·
                  refine ⟨733188300514999136233325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 488792200343332757488883 733188300514999136233325)
                  ·
                    refine ⟨274945612693124676087497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 733188300514999136233325 274945612693124676087497)
                    ·
                      refine ⟨206209209519843507065623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 274945612693124676087497 206209209519843507065623)
                      ·
                        rfl

theorem cell23_401591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 1, 1, 3, 2].length) (baseStart_401591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401591 prefixEnd_401591 := by exact prefixLift 401591
  have htrace : WordTrace (prefixWord ++ tailWord_401591) baseStart_401591 baseEnd_401591 := by
    simpa [prefixWord, tailWord_401591, baseEnd_401591] using wordTrace_append hprefix tailTrace_401591
  have hstable : (prefixWord ++ tailWord_401591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401591).length < 2 ^ (prefixWord ++ tailWord_401591).sum := by decide
  have hdescent : baseEnd_401591 < baseStart_401591 := by decide
  rcases family_descends (prefixWord ++ tailWord_401591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401610 : List Nat := [3, 1, 2, 1, 3, 1, 2, 3, 7]
def baseStart_401610 : Nat := 118140960795 + 401610 * 2 ^ 59
def prefixEnd_401610 : Nat := 4983230072969 + 3 ^ 40 * 401610 * 2
def baseEnd_401610 : Nat := 22913218405808770303115

theorem tailTrace_401610 : CollatzResearch.WordTrace tailWord_401610 prefixEnd_401610 22913218405808770303115 := by
  unfold tailWord_401610
  simp only [CollatzResearch.WordTrace]
  refine ⟨3661980018760758593104571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9765280050028689581612189 3661980018760758593104571)
  ·
    refine ⟨5492970028141137889656857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3661980018760758593104571 5492970028141137889656857)
    ·
      refine ⟨4119727521105853417242643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5492970028141137889656857 4119727521105853417242643)
      ·
        refine ⟨6179591281658780125863965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4119727521105853417242643 6179591281658780125863965)
        ·
          refine ⟨2317346730622042547198987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6179591281658780125863965 2317346730622042547198987)
          ·
            refine ⟨3476020095933063820798481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2317346730622042547198987 3476020095933063820798481)
            ·
              refine ⟨2607015071949797865598861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3476020095933063820798481 2607015071949797865598861)
              ·
                refine ⟨977630651981174199599573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2607015071949797865598861 977630651981174199599573)
                ·
                  refine ⟨22913218405808770303115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 977630651981174199599573 22913218405808770303115)
                  ·
                    rfl

theorem cell23_401610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 7].length) (baseStart_401610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401610 prefixEnd_401610 := by exact prefixLift 401610
  have htrace : WordTrace (prefixWord ++ tailWord_401610) baseStart_401610 baseEnd_401610 := by
    simpa [prefixWord, tailWord_401610, baseEnd_401610] using wordTrace_append hprefix tailTrace_401610
  have hstable : (prefixWord ++ tailWord_401610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401610).length < 2 ^ (prefixWord ++ tailWord_401610).sum := by decide
  have hdescent : baseEnd_401610 < baseStart_401610 := by decide
  rcases family_descends (prefixWord ++ tailWord_401610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401621 : List Nat := [1, 3, 2, 4, 2, 1, 2, 1, 1, 4, 2]
def baseStart_401621 : Nat := 118140960795 + 401621 * 2 ^ 59
def prefixEnd_401621 : Nat := 4983230072969 + 3 ^ 40 * 401621 * 2
def baseEnd_401621 : Nat := 206224613939478389690485

theorem tailTrace_401621 : CollatzResearch.WordTrace tailWord_401621 prefixEnd_401621 206224613939478389690485 := by
  unfold tailWord_401621
  simp only [CollatzResearch.WordTrace]
  refine ⟨14648321278003183251068717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9765547518668788834045811 14648321278003183251068717)
  ·
    refine ⟨5493120479251193719150769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14648321278003183251068717 5493120479251193719150769)
    ·
      refine ⟨4119840359438395289363077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5493120479251193719150769 4119840359438395289363077)
      ·
        refine ⟨772470067394699116755577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4119840359438395289363077 772470067394699116755577)
        ·
          refine ⟨579352550546024337566683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 772470067394699116755577 579352550546024337566683)
          ·
            refine ⟨869028825819036506350025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 579352550546024337566683 869028825819036506350025)
            ·
              refine ⟨651771619364277379762519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 869028825819036506350025 651771619364277379762519)
              ·
                refine ⟨977657429046416069643779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 651771619364277379762519 977657429046416069643779)
                ·
                  refine ⟨1466486143569624104465669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 977657429046416069643779 1466486143569624104465669)
                  ·
                    refine ⟨274966151919304519587313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1466486143569624104465669 274966151919304519587313)
                    ·
                      refine ⟨206224613939478389690485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 274966151919304519587313 206224613939478389690485)
                      ·
                        rfl

theorem cell23_401621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_401621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401621 prefixEnd_401621 := by exact prefixLift 401621
  have htrace : WordTrace (prefixWord ++ tailWord_401621) baseStart_401621 baseEnd_401621 := by
    simpa [prefixWord, tailWord_401621, baseEnd_401621] using wordTrace_append hprefix tailTrace_401621
  have hstable : (prefixWord ++ tailWord_401621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401621).length < 2 ^ (prefixWord ++ tailWord_401621).sum := by decide
  have hdescent : baseEnd_401621 < baseStart_401621 := by decide
  rcases family_descends (prefixWord ++ tailWord_401621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401697 : List Nat := [1, 2, 3, 2, 1, 1, 4, 1, 1, 4, 3]
def baseStart_401697 : Nat := 118140960795 + 401697 * 2 ^ 59
def prefixEnd_401697 : Nat := 4983230072969 + 3 ^ 40 * 401697 * 2
def baseEnd_401697 : Nat := 206263638469220092340135

theorem tailTrace_401697 : CollatzResearch.WordTrace tailWord_401697 prefixEnd_401697 206263638469220092340135 := by
  unfold tailWord_401697
  simp only [CollatzResearch.WordTrace]
  refine ⟨14651093225727848230835345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9767395483818565487223563 14651093225727848230835345)
  ·
    refine ⟨10988319919295886173126509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14651093225727848230835345 10988319919295886173126509)
    ·
      refine ⟨4120619969735957314922441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10988319919295886173126509 4120619969735957314922441)
      ·
        refine ⟨3090464977301967986191831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4120619969735957314922441 3090464977301967986191831)
        ·
          refine ⟨4635697465952951979287747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3090464977301967986191831 4635697465952951979287747)
          ·
            refine ⟨6953546198929427968931621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4635697465952951979287747 6953546198929427968931621)
            ·
              refine ⟨1303789912299267744174679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6953546198929427968931621 1303789912299267744174679)
              ·
                refine ⟨1955684868448901616262019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1303789912299267744174679 1955684868448901616262019)
                ·
                  refine ⟨2933527302673352424393029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1955684868448901616262019 2933527302673352424393029)
                  ·
                    refine ⟨550036369251253579573693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2933527302673352424393029 550036369251253579573693)
                    ·
                      refine ⟨206263638469220092340135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 550036369251253579573693 206263638469220092340135)
                      ·
                        rfl

theorem cell23_401697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_401697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401697 prefixEnd_401697 := by exact prefixLift 401697
  have htrace : WordTrace (prefixWord ++ tailWord_401697) baseStart_401697 baseEnd_401697 := by
    simpa [prefixWord, tailWord_401697, baseEnd_401697] using wordTrace_append hprefix tailTrace_401697
  have hstable : (prefixWord ++ tailWord_401697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401697).length < 2 ^ (prefixWord ++ tailWord_401697).sum := by decide
  have hdescent : baseEnd_401697 < baseStart_401697 := by decide
  rcases family_descends (prefixWord ++ tailWord_401697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401717 : List Nat := [1, 3, 3, 1, 2, 1, 2, 4, 6]
def baseStart_401717 : Nat := 118140960795 + 401717 * 2 ^ 59
def prefixEnd_401717 : Nat := 4983230072969 + 3 ^ 40 * 401717 * 2
def baseEnd_401717 : Nat := 22919323120256668232227

theorem tailTrace_401717 : CollatzResearch.WordTrace tailWord_401717 prefixEnd_401717 22919323120256668232227 := by
  unfold tailWord_401717
  simp only [CollatzResearch.WordTrace]
  refine ⟨14651822685655391646563405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9767881790436927764375603 14651822685655391646563405)
  ·
    refine ⟨5494433507120771867461277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14651822685655391646563405 5494433507120771867461277)
    ·
      refine ⟨2060412565170289450297979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5494433507120771867461277 2060412565170289450297979)
      ·
        refine ⟨3090618847755434175446969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2060412565170289450297979 3090618847755434175446969)
        ·
          refine ⟨2317964135816575631585227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3090618847755434175446969 2317964135816575631585227)
          ·
            refine ⟨3476946203724863447377841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2317964135816575631585227 3476946203724863447377841)
            ·
              refine ⟨2607709652793647585533381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3476946203724863447377841 2607709652793647585533381)
              ·
                refine ⟨488945559898808922287509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2607709652793647585533381 488945559898808922287509)
                ·
                  refine ⟨22919323120256668232227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 488945559898808922287509 22919323120256668232227)
                  ·
                    rfl

theorem cell23_401717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4, 6].length) (baseStart_401717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401717 prefixEnd_401717 := by exact prefixLift 401717
  have htrace : WordTrace (prefixWord ++ tailWord_401717) baseStart_401717 baseEnd_401717 := by
    simpa [prefixWord, tailWord_401717, baseEnd_401717] using wordTrace_append hprefix tailTrace_401717
  have hstable : (prefixWord ++ tailWord_401717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401717).length < 2 ^ (prefixWord ++ tailWord_401717).sum := by decide
  have hdescent : baseEnd_401717 < baseStart_401717 := by decide
  rcases family_descends (prefixWord ++ tailWord_401717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401720 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 1, 1, 8]
def baseStart_401720 : Nat := 118140960795 + 401720 * 2 ^ 59
def prefixEnd_401720 : Nat := 4983230072969 + 3 ^ 40 * 401720 * 2
def baseEnd_401720 : Nat := 206275448524273502352529

theorem tailTrace_401720 : CollatzResearch.WordTrace tailWord_401720 prefixEnd_401720 206275448524273502352529 := by
  unfold tailWord_401720
  simp only [CollatzResearch.WordTrace]
  refine ⟨7325966052322261579461307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9767954736429682105948409 7325966052322261579461307)
  ·
    refine ⟨10988949078483392369191961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7325966052322261579461307 10988949078483392369191961)
    ·
      refine ⟨8241711808862544276893971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10988949078483392369191961 8241711808862544276893971)
      ·
        refine ⟨12362567713293816415340957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8241711808862544276893971 12362567713293816415340957)
        ·
          refine ⟨4635962892485181155752859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12362567713293816415340957 4635962892485181155752859)
          ·
            refine ⟨6953944338727771733629289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4635962892485181155752859 6953944338727771733629289)
            ·
              refine ⟨5215458254045828800221967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6953944338727771733629289 5215458254045828800221967)
              ·
                refine ⟨7823187381068743200332951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5215458254045828800221967 7823187381068743200332951)
                ·
                  refine ⟨11734781071603114800499427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7823187381068743200332951 11734781071603114800499427)
                  ·
                    refine ⟨17602171607404672200749141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11734781071603114800499427 17602171607404672200749141)
                    ·
                      refine ⟨206275448524273502352529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 17602171607404672200749141 206275448524273502352529)
                      ·
                        rfl

theorem cell23_401720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_401720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401720 prefixEnd_401720 := by exact prefixLift 401720
  have htrace : WordTrace (prefixWord ++ tailWord_401720) baseStart_401720 baseEnd_401720 := by
    simpa [prefixWord, tailWord_401720, baseEnd_401720] using wordTrace_append hprefix tailTrace_401720
  have hstable : (prefixWord ++ tailWord_401720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401720).length < 2 ^ (prefixWord ++ tailWord_401720).sum := by decide
  have hdescent : baseEnd_401720 < baseStart_401720 := by decide
  rcases family_descends (prefixWord ++ tailWord_401720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401721 : List Nat := [1, 2, 1, 6, 1, 3, 1, 1, 3, 4]
def baseStart_401721 : Nat := 118140960795 + 401721 * 2 ^ 59
def prefixEnd_401721 : Nat := 4983230072969 + 3 ^ 40 * 401721 * 2
def baseEnd_401721 : Nat := 68758654001642666146675

theorem tailTrace_401721 : CollatzResearch.WordTrace tailWord_401721 prefixEnd_401721 68758654001642666146675 := by
  unfold tailWord_401721
  simp only [CollatzResearch.WordTrace]
  refine ⟨14651968577640900329709017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9767979051760600219806011 14651968577640900329709017)
  ·
    refine ⟨10988976433230675247281763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14651968577640900329709017 10988976433230675247281763)
    ·
      refine ⟨16483464649846012870922645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10988976433230675247281763 16483464649846012870922645)
      ·
        refine ⟨772662405461531853324499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16483464649846012870922645 772662405461531853324499)
        ·
          refine ⟨1158993608192297779986749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 772662405461531853324499 1158993608192297779986749)
          ·
            refine ⟨434622603072111667495031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1158993608192297779986749 434622603072111667495031)
            ·
              refine ⟨651933904608167501242547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 434622603072111667495031 651933904608167501242547)
              ·
                refine ⟨977900856912251251863821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 651933904608167501242547 977900856912251251863821)
                ·
                  refine ⟨366712821342094219448933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 977900856912251251863821 366712821342094219448933)
                  ·
                    refine ⟨68758654001642666146675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 366712821342094219448933 68758654001642666146675)
                    ·
                      rfl

theorem cell23_401721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 3, 4].length) (baseStart_401721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401721 prefixEnd_401721 := by exact prefixLift 401721
  have htrace : WordTrace (prefixWord ++ tailWord_401721) baseStart_401721 baseEnd_401721 := by
    simpa [prefixWord, tailWord_401721, baseEnd_401721] using wordTrace_append hprefix tailTrace_401721
  have hstable : (prefixWord ++ tailWord_401721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401721).length < 2 ^ (prefixWord ++ tailWord_401721).sum := by decide
  have hdescent : baseEnd_401721 < baseStart_401721 := by decide
  rcases family_descends (prefixWord ++ tailWord_401721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401747 : List Nat := [1, 1, 1, 2, 1, 1, 4, 6, 1, 5]
def baseStart_401747 : Nat := 118140960795 + 401747 * 2 ^ 59
def prefixEnd_401747 : Nat := 4983230072969 + 3 ^ 40 * 401747 * 2
def baseEnd_401747 : Nat := 68763104167314965571635

theorem tailTrace_401747 : CollatzResearch.WordTrace tailWord_401747 prefixEnd_401747 68763104167314965571635 := by
  unfold tailWord_401747
  simp only [CollatzResearch.WordTrace]
  refine ⟨14652916875546706770155495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9768611250364471180103663 14652916875546706770155495)
  ·
    refine ⟨21979375313320060155233243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14652916875546706770155495 21979375313320060155233243)
    ·
      refine ⟨32969062969980090232849865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21979375313320060155233243 32969062969980090232849865)
      ·
        refine ⟨24726797227485067674637399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32969062969980090232849865 24726797227485067674637399)
        ·
          refine ⟨37090195841227601511956099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24726797227485067674637399 37090195841227601511956099)
          ·
            refine ⟨55635293761841402267934149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37090195841227601511956099 55635293761841402267934149)
            ·
              refine ⟨10431617580345262925237653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55635293761841402267934149 10431617580345262925237653)
              ·
                refine ⟨488982074078684199620515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10431617580345262925237653 488982074078684199620515)
                ·
                  refine ⟨733473111118026299430773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 488982074078684199620515 733473111118026299430773)
                  ·
                    refine ⟨68763104167314965571635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 733473111118026299430773 68763104167314965571635)
                    ·
                      rfl

theorem cell23_401747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6, 1, 5].length) (baseStart_401747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401747 prefixEnd_401747 := by exact prefixLift 401747
  have htrace : WordTrace (prefixWord ++ tailWord_401747) baseStart_401747 baseEnd_401747 := by
    simpa [prefixWord, tailWord_401747, baseEnd_401747] using wordTrace_append hprefix tailTrace_401747
  have hstable : (prefixWord ++ tailWord_401747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401747).length < 2 ^ (prefixWord ++ tailWord_401747).sum := by decide
  have hdescent : baseEnd_401747 < baseStart_401747 := by decide
  rcases family_descends (prefixWord ++ tailWord_401747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401778 : List Nat := [3, 2, 1, 2, 1, 4, 1, 4, 1, 1, 3]
def baseStart_401778 : Nat := 118140960795 + 401778 * 2 ^ 59
def prefixEnd_401778 : Nat := 4983230072969 + 3 ^ 40 * 401778 * 2
def baseEnd_401778 : Nat := 206305230402234275427263

theorem tailTrace_401778 : CollatzResearch.WordTrace tailWord_401778 prefixEnd_401778 206305230402234275427263 := by
  unfold tailWord_401778
  simp only [CollatzResearch.WordTrace]
  refine ⟨3663511884608599766133497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9769365025622932709689325 3663511884608599766133497)
  ·
    refine ⟨2747633913456449824600123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3663511884608599766133497 2747633913456449824600123)
    ·
      refine ⟨4121450870184674736900185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2747633913456449824600123 4121450870184674736900185)
      ·
        refine ⟨3091088152638506052675139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4121450870184674736900185 3091088152638506052675139)
        ·
          refine ⟨4636632228957759079012709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3091088152638506052675139 4636632228957759079012709)
          ·
            refine ⟨869368542929579827314883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4636632228957759079012709 869368542929579827314883)
            ·
              refine ⟨1304052814394369740972325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 869368542929579827314883 1304052814394369740972325)
              ·
                refine ⟨244509902698944326432311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1304052814394369740972325 244509902698944326432311)
                ·
                  refine ⟨366764854048416489648467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 244509902698944326432311 366764854048416489648467)
                  ·
                    refine ⟨550147281072624734472701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 366764854048416489648467 550147281072624734472701)
                    ·
                      refine ⟨206305230402234275427263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 550147281072624734472701 206305230402234275427263)
                      ·
                        rfl

theorem cell23_401778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 4, 1, 1, 3].length) (baseStart_401778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401778 prefixEnd_401778 := by exact prefixLift 401778
  have htrace : WordTrace (prefixWord ++ tailWord_401778) baseStart_401778 baseEnd_401778 := by
    simpa [prefixWord, tailWord_401778, baseEnd_401778] using wordTrace_append hprefix tailTrace_401778
  have hstable : (prefixWord ++ tailWord_401778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401778).length < 2 ^ (prefixWord ++ tailWord_401778).sum := by decide
  have hdescent : baseEnd_401778 < baseStart_401778 := by decide
  rcases family_descends (prefixWord ++ tailWord_401778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401801 : List Nat := [1, 2, 1, 1, 6, 1, 1, 1, 5, 2, 2]
def baseStart_401801 : Nat := 118140960795 + 401801 * 2 ^ 59
def prefixEnd_401801 : Nat := 4983230072969 + 3 ^ 40 * 401801 * 2
def baseEnd_401801 : Nat := 206317040457287685439657

theorem tailTrace_401801 : CollatzResearch.WordTrace tailWord_401801 prefixEnd_401801 206317040457287685439657 := by
  unfold tailWord_401801
  simp only [CollatzResearch.WordTrace]
  refine ⟨14654886417351073992621257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9769924278234049328414171 14654886417351073992621257)
  ·
    refine ⟨10991164813013305494465943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14654886417351073992621257 10991164813013305494465943)
    ·
      refine ⟨16486747219519958241698915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10991164813013305494465943 16486747219519958241698915)
      ·
        refine ⟨24730120829279937362548373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16486747219519958241698915 24730120829279937362548373)
        ·
          refine ⟨1159224413872497063869455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24730120829279937362548373 1159224413872497063869455)
          ·
            refine ⟨1738836620808745595804183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1159224413872497063869455 1738836620808745595804183)
            ·
              refine ⟨2608254931213118393706275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1738836620808745595804183 2608254931213118393706275)
              ·
                refine ⟨3912382396819677590559413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2608254931213118393706275 3912382396819677590559413)
                ·
                  refine ⟨366785849701844774114945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3912382396819677590559413 366785849701844774114945)
                  ·
                    refine ⟨275089387276383580586209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 366785849701844774114945 275089387276383580586209)
                    ·
                      refine ⟨206317040457287685439657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 275089387276383580586209 206317040457287685439657)
                      ·
                        rfl

theorem cell23_401801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 5, 2, 2].length) (baseStart_401801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401801 prefixEnd_401801 := by exact prefixLift 401801
  have htrace : WordTrace (prefixWord ++ tailWord_401801) baseStart_401801 baseEnd_401801 := by
    simpa [prefixWord, tailWord_401801, baseEnd_401801] using wordTrace_append hprefix tailTrace_401801
  have hstable : (prefixWord ++ tailWord_401801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401801).length < 2 ^ (prefixWord ++ tailWord_401801).sum := by decide
  have hdescent : baseEnd_401801 < baseStart_401801 := by decide
  rcases family_descends (prefixWord ++ tailWord_401801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401804 : List Nat := [2, 2, 1, 2, 1, 4, 2, 1, 3, 2, 3]
def baseStart_401804 : Nat := 118140960795 + 401804 * 2 ^ 59
def prefixEnd_401804 : Nat := 4983230072969 + 3 ^ 40 * 401804 * 2
def baseEnd_401804 : Nat := 206318580899251173702143

theorem tailTrace_401804 : CollatzResearch.WordTrace tailWord_401804 prefixEnd_401804 206318580899251173702143 := by
  unfold tailWord_401804
  simp only [CollatzResearch.WordTrace]
  refine ⟨7327497918170102752490233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9769997224226803669986977 7327497918170102752490233)
  ·
    refine ⟨5495623438627577064367675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7327497918170102752490233 5495623438627577064367675)
    ·
      refine ⟨8243435157941365596551513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5495623438627577064367675 8243435157941365596551513)
      ·
        refine ⟨6182576368456024197413635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8243435157941365596551513 6182576368456024197413635)
        ·
          refine ⟨9273864552684036296120453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6182576368456024197413635 9273864552684036296120453)
          ·
            refine ⟨1738849603628256805522585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9273864552684036296120453 1738849603628256805522585)
            ·
              refine ⟨1304137202721192604141939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1738849603628256805522585 1304137202721192604141939)
              ·
                refine ⟨1956205804081788906212909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1304137202721192604141939 1956205804081788906212909)
                ·
                  refine ⟨733577176530670839829841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1956205804081788906212909 733577176530670839829841)
                  ·
                    refine ⟨550182882398003129872381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 733577176530670839829841 550182882398003129872381)
                    ·
                      refine ⟨206318580899251173702143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 550182882398003129872381 206318580899251173702143)
                      ·
                        rfl

theorem cell23_401804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 3, 2, 3].length) (baseStart_401804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401804 prefixEnd_401804 := by exact prefixLift 401804
  have htrace : WordTrace (prefixWord ++ tailWord_401804) baseStart_401804 baseEnd_401804 := by
    simpa [prefixWord, tailWord_401804, baseEnd_401804] using wordTrace_append hprefix tailTrace_401804
  have hstable : (prefixWord ++ tailWord_401804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401804).length < 2 ^ (prefixWord ++ tailWord_401804).sum := by decide
  have hdescent : baseEnd_401804 < baseStart_401804 := by decide
  rcases family_descends (prefixWord ++ tailWord_401804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401818 : List Nat := [3, 1, 1, 4, 1, 4, 2, 1, 1, 1, 4]
def baseStart_401818 : Nat := 118140960795 + 401818 * 2 ^ 59
def prefixEnd_401818 : Nat := 4983230072969 + 3 ^ 40 * 401818 * 2
def baseEnd_401818 : Nat := 206325769628414118927079

theorem tailTrace_401818 : CollatzResearch.WordTrace tailWord_401818 prefixEnd_401818 206325769628414118927079 := by
  unfold tailWord_401818
  simp only [CollatzResearch.WordTrace]
  refine ⟨3663876614572371473997527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9770337638859657263993405 3663876614572371473997527)
  ·
    refine ⟨5495814921858557210996291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3663876614572371473997527 5495814921858557210996291)
    ·
      refine ⟨8243722382787835816494437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5495814921858557210996291 8243722382787835816494437)
      ·
        refine ⟨1545697946772719215592707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8243722382787835816494437 1545697946772719215592707)
        ·
          refine ⟨2318546920159078823389061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1545697946772719215592707 2318546920159078823389061)
          ·
            refine ⟨434727547529827279385449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2318546920159078823389061 434727547529827279385449)
            ·
              refine ⟨326045660647370459539087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 434727547529827279385449 326045660647370459539087)
              ·
                refine ⟨489068490971055689308631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 326045660647370459539087 489068490971055689308631)
                ·
                  refine ⟨733602736456583533962947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 489068490971055689308631 733602736456583533962947)
                  ·
                    refine ⟨1100404104684875300944421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 733602736456583533962947 1100404104684875300944421)
                    ·
                      refine ⟨206325769628414118927079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1100404104684875300944421 206325769628414118927079)
                      ·
                        rfl

theorem cell23_401818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_401818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401818 prefixEnd_401818 := by exact prefixLift 401818
  have htrace : WordTrace (prefixWord ++ tailWord_401818) baseStart_401818 baseEnd_401818 := by
    simpa [prefixWord, tailWord_401818, baseEnd_401818] using wordTrace_append hprefix tailTrace_401818
  have hstable : (prefixWord ++ tailWord_401818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401818).length < 2 ^ (prefixWord ++ tailWord_401818).sum := by decide
  have hdescent : baseEnd_401818 < baseStart_401818 := by decide
  rcases family_descends (prefixWord ++ tailWord_401818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401897 : List Nat := [1, 2, 1, 1, 1, 2, 1, 7, 7]
def baseStart_401897 : Nat := 118140960795 + 401897 * 2 ^ 59
def prefixEnd_401897 : Nat := 4983230072969 + 3 ^ 40 * 401897 * 2
def baseEnd_401897 : Nat := 22929592733346589982135

theorem tailTrace_401897 : CollatzResearch.WordTrace tailWord_401897 prefixEnd_401897 22929592733346589982135 := by
  unfold tailWord_401897
  simp only [CollatzResearch.WordTrace]
  refine ⟨14658387825003282388115945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9772258550002188258743963 14658387825003282388115945)
  ·
    refine ⟨10993790868752461791086959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14658387825003282388115945 10993790868752461791086959)
    ·
      refine ⟨16490686303128692686630439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10993790868752461791086959 16490686303128692686630439)
      ·
        refine ⟨24736029454693039029945659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16490686303128692686630439 24736029454693039029945659)
        ·
          refine ⟨37104044182039558544918489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24736029454693039029945659 37104044182039558544918489)
          ·
            refine ⟨27828033136529668908688867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37104044182039558544918489 27828033136529668908688867)
            ·
              refine ⟨41742049704794503363033301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27828033136529668908688867 41742049704794503363033301)
              ·
                refine ⟨978329289956121172571093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 41742049704794503363033301 978329289956121172571093)
                ·
                  refine ⟨22929592733346589982135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 978329289956121172571093 22929592733346589982135)
                  ·
                    rfl

theorem cell23_401897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 7].length) (baseStart_401897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401897 prefixEnd_401897 := by exact prefixLift 401897
  have htrace : WordTrace (prefixWord ++ tailWord_401897) baseStart_401897 baseEnd_401897 := by
    simpa [prefixWord, tailWord_401897, baseEnd_401897] using wordTrace_append hprefix tailTrace_401897
  have hstable : (prefixWord ++ tailWord_401897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401897).length < 2 ^ (prefixWord ++ tailWord_401897).sum := by decide
  have hdescent : baseEnd_401897 < baseStart_401897 := by decide
  rcases family_descends (prefixWord ++ tailWord_401897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401948 : List Nat := [2, 2, 3, 1, 2, 2, 4, 2, 5]
def baseStart_401948 : Nat := 118140960795 + 401948 * 2 ^ 59
def prefixEnd_401948 : Nat := 4983230072969 + 3 ^ 40 * 401948 * 2
def baseEnd_401948 : Nat := 22932502457055401144609

theorem tailTrace_401948 : CollatzResearch.WordTrace tailWord_401948 prefixEnd_401948 22932502457055401144609 := by
  unfold tailWord_401948
  simp only [CollatzResearch.WordTrace]
  refine ⟨7330123973909259049111249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9773498631879012065481665 7330123973909259049111249)
  ·
    refine ⟨5497592980431944286833437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7330123973909259049111249 5497592980431944286833437)
    ·
      refine ⟨2061597367661979107562539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5497592980431944286833437 2061597367661979107562539)
      ·
        refine ⟨3092396051492968661343809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2061597367661979107562539 3092396051492968661343809)
        ·
          refine ⟨2319297038619726496007857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3092396051492968661343809 2319297038619726496007857)
          ·
            refine ⟨1739472778964794872005893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2319297038619726496007857 1739472778964794872005893)
            ·
              refine ⟨326151146055899038501105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1739472778964794872005893 326151146055899038501105)
              ·
                refine ⟨244613359541924278875829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 326151146055899038501105 244613359541924278875829)
                ·
                  refine ⟨22932502457055401144609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 244613359541924278875829 22932502457055401144609)
                  ·
                    rfl

theorem cell23_401948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 2, 5].length) (baseStart_401948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401948 prefixEnd_401948 := by exact prefixLift 401948
  have htrace : WordTrace (prefixWord ++ tailWord_401948) baseStart_401948 baseEnd_401948 := by
    simpa [prefixWord, tailWord_401948, baseEnd_401948] using wordTrace_append hprefix tailTrace_401948
  have hstable : (prefixWord ++ tailWord_401948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401948).length < 2 ^ (prefixWord ++ tailWord_401948).sum := by decide
  have hdescent : baseEnd_401948 < baseStart_401948 := by decide
  rcases family_descends (prefixWord ++ tailWord_401948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401964 : List Nat := [2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 4]
def baseStart_401964 : Nat := 118140960795 + 401964 * 2 ^ 59
def prefixEnd_401964 : Nat := 4983230072969 + 3 ^ 40 * 401964 * 2
def baseEnd_401964 : Nat := 206400737803970547701407

theorem tailTrace_401964 : CollatzResearch.WordTrace tailWord_401964 prefixEnd_401964 206400737803970547701407 := by
  unfold tailWord_401964
  simp only [CollatzResearch.WordTrace]
  refine ⟨7330415757880276415402473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9773887677173701887203297 7330415757880276415402473)
  ·
    refine ⟨5497811818410207311551855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7330415757880276415402473 5497811818410207311551855)
    ·
      refine ⟨8246717727615310967327783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5497811818410207311551855 8246717727615310967327783)
      ·
        refine ⟨12370076591422966450991675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8246717727615310967327783 12370076591422966450991675)
        ·
          refine ⟨18555114887134449676487513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12370076591422966450991675 18555114887134449676487513)
          ·
            refine ⟨13916336165350837257365635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18555114887134449676487513 13916336165350837257365635)
            ·
              refine ⟨20874504248026255886048453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13916336165350837257365635 20874504248026255886048453)
              ·
                refine ⟨3913969546504922978634085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20874504248026255886048453 3913969546504922978634085)
                ·
                  refine ⟨733869289969673058493891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3913969546504922978634085 733869289969673058493891)
                  ·
                    refine ⟨1100803934954509587740837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 733869289969673058493891 1100803934954509587740837)
                    ·
                      refine ⟨206400737803970547701407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1100803934954509587740837 206400737803970547701407)
                      ·
                        rfl

theorem cell23_401964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 4].length) (baseStart_401964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401964 prefixEnd_401964 := by exact prefixLift 401964
  have htrace : WordTrace (prefixWord ++ tailWord_401964) baseStart_401964 baseEnd_401964 := by
    simpa [prefixWord, tailWord_401964, baseEnd_401964] using wordTrace_append hprefix tailTrace_401964
  have hstable : (prefixWord ++ tailWord_401964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401964).length < 2 ^ (prefixWord ++ tailWord_401964).sum := by decide
  have hdescent : baseEnd_401964 < baseStart_401964 := by decide
  rcases family_descends (prefixWord ++ tailWord_401964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401965 : List Nat := [1, 5, 4, 1, 1, 1, 1, 2, 7]
def baseStart_401965 : Nat := 118140960795 + 401965 * 2 ^ 59
def prefixEnd_401965 : Nat := 4983230072969 + 3 ^ 40 * 401965 * 2
def baseEnd_401965 : Nat := 22933472364958338198767

theorem tailTrace_401965 : CollatzResearch.WordTrace tailWord_401965 prefixEnd_401965 22933472364958338198767 := by
  unfold tailWord_401965
  simp only [CollatzResearch.WordTrace]
  refine ⟨14660867988756930001591349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9773911992504620001060899 14660867988756930001591349)
  ·
    refine ⟨1374456373945962187649189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14660867988756930001591349 1374456373945962187649189)
    ·
      refine ⟨257710570114867910184223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1374456373945962187649189 257710570114867910184223)
      ·
        refine ⟨386565855172301865276335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257710570114867910184223 386565855172301865276335)
        ·
          refine ⟨579848782758452797914503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386565855172301865276335 579848782758452797914503)
          ·
            refine ⟨869773174137679196871755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 579848782758452797914503 869773174137679196871755)
            ·
              refine ⟨1304659761206518795307633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 869773174137679196871755 1304659761206518795307633)
              ·
                refine ⟨978494820904889096480725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1304659761206518795307633 978494820904889096480725)
                ·
                  refine ⟨22933472364958338198767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 978494820904889096480725 22933472364958338198767)
                  ·
                    rfl

theorem cell23_401965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_401965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401965 prefixEnd_401965 := by exact prefixLift 401965
  have htrace : WordTrace (prefixWord ++ tailWord_401965) baseStart_401965 baseEnd_401965 := by
    simpa [prefixWord, tailWord_401965, baseEnd_401965] using wordTrace_append hprefix tailTrace_401965
  have hstable : (prefixWord ++ tailWord_401965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401965).length < 2 ^ (prefixWord ++ tailWord_401965).sum := by decide
  have hdescent : baseEnd_401965 < baseStart_401965 := by decide
  rcases family_descends (prefixWord ++ tailWord_401965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401981 : List Nat := [1, 4, 1, 3, 2, 2, 1, 1, 1, 3, 4]
def baseStart_401981 : Nat := 118140960795 + 401981 * 2 ^ 59
def prefixEnd_401981 : Nat := 4983230072969 + 3 ^ 40 * 401981 * 2
def baseEnd_401981 : Nat := 206409466975096981188829

theorem tailTrace_401981 : CollatzResearch.WordTrace tailWord_401981 prefixEnd_401981 206409466975096981188829 := by
  unfold tailWord_401981
  simp only [CollatzResearch.WordTrace]
  refine ⟨14661451556698964734173797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9774301037799309822782531 14661451556698964734173797)
  ·
    refine ⟨2749022166881055887657587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14661451556698964734173797 2749022166881055887657587)
    ·
      refine ⟨4123533250321583831486381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2749022166881055887657587 4123533250321583831486381)
      ·
        refine ⟨1546324968870593936807393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4123533250321583831486381 1546324968870593936807393)
        ·
          refine ⟨1159743726652945452605545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1546324968870593936807393 1159743726652945452605545)
          ·
            refine ⟨869807794989709089454159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1159743726652945452605545 869807794989709089454159)
            ·
              refine ⟨1304711692484563634181239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 869807794989709089454159 1304711692484563634181239)
              ·
                refine ⟨1957067538726845451271859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1304711692484563634181239 1957067538726845451271859)
                ·
                  refine ⟨2935601308090268176907789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1957067538726845451271859 2935601308090268176907789)
                  ·
                    refine ⟨1100850490533850566340421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2935601308090268176907789 1100850490533850566340421)
                    ·
                      refine ⟨206409466975096981188829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1100850490533850566340421 206409466975096981188829)
                      ·
                        rfl

theorem cell23_401981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_401981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401981 prefixEnd_401981 := by exact prefixLift 401981
  have htrace : WordTrace (prefixWord ++ tailWord_401981) baseStart_401981 baseEnd_401981 := by
    simpa [prefixWord, tailWord_401981, baseEnd_401981] using wordTrace_append hprefix tailTrace_401981
  have hstable : (prefixWord ++ tailWord_401981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401981).length < 2 ^ (prefixWord ++ tailWord_401981).sum := by decide
  have hdescent : baseEnd_401981 < baseStart_401981 := by decide
  rcases family_descends (prefixWord ++ tailWord_401981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401994 : List Nat := [3, 1, 2, 1, 1, 4, 1, 1, 2, 1, 6]
def baseStart_401994 : Nat := 118140960795 + 401994 * 2 ^ 59
def prefixEnd_401994 : Nat := 4983230072969 + 3 ^ 40 * 401994 * 2
def baseEnd_401994 : Nat := 206416142223605430326269

theorem tailTrace_401994 : CollatzResearch.WordTrace tailWord_401994 prefixEnd_401994 206416142223605430326269 := by
  unfold tailWord_401994
  simp only [CollatzResearch.WordTrace]
  refine ⟨3665481426412966988599259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9774617137101245302931357 3665481426412966988599259)
  ·
    refine ⟨5498222139619450482898889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3665481426412966988599259 5498222139619450482898889)
    ·
      refine ⟨4123666604714587862174167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5498222139619450482898889 4123666604714587862174167)
      ·
        refine ⟨6185499907071881793261251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4123666604714587862174167 6185499907071881793261251)
        ·
          refine ⟨9278249860607822689891877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6185499907071881793261251 9278249860607822689891877)
          ·
            refine ⟨1739671848863966754354727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9278249860607822689891877 1739671848863966754354727)
            ·
              refine ⟨2609507773295950131532091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1739671848863966754354727 2609507773295950131532091)
              ·
                refine ⟨3914261659943925197298137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2609507773295950131532091 3914261659943925197298137)
                ·
                  refine ⟨2935696244957943897973603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3914261659943925197298137 2935696244957943897973603)
                  ·
                    refine ⟨4403544367436915846960405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2935696244957943897973603 4403544367436915846960405)
                    ·
                      refine ⟨206416142223605430326269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4403544367436915846960405 206416142223605430326269)
                      ·
                        rfl

theorem cell23_401994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_401994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_401994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_401994 prefixEnd_401994 := by exact prefixLift 401994
  have htrace : WordTrace (prefixWord ++ tailWord_401994) baseStart_401994 baseEnd_401994 := by
    simpa [prefixWord, tailWord_401994, baseEnd_401994] using wordTrace_append hprefix tailTrace_401994
  have hstable : (prefixWord ++ tailWord_401994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401994).length < 2 ^ (prefixWord ++ tailWord_401994).sum := by decide
  have hdescent : baseEnd_401994 < baseStart_401994 := by decide
  rcases family_descends (prefixWord ++ tailWord_401994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402008 : List Nat := [2, 1, 2, 2, 1, 2, 4, 4, 1, 4]
def baseStart_402008 : Nat := 118140960795 + 402008 * 2 ^ 59
def prefixEnd_402008 : Nat := 4983230072969 + 3 ^ 40 * 402008 * 2
def baseEnd_402008 : Nat := 68807776984256125183735

theorem tailTrace_402008 : CollatzResearch.WordTrace tailWord_402008 prefixEnd_402008 68807776984256125183735 := by
  unfold tailWord_402008
  simp only [CollatzResearch.WordTrace]
  refine ⟨7331218163800574172703339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9774957551734098896937785 7331218163800574172703339)
  ·
    refine ⟨10996827245700861259055009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7331218163800574172703339 10996827245700861259055009)
    ·
      refine ⟨8247620434275645944291257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10996827245700861259055009 8247620434275645944291257)
      ·
        refine ⟨6185715325706734458218443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8247620434275645944291257 6185715325706734458218443)
        ·
          refine ⟨9278572988560101687327665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6185715325706734458218443 9278572988560101687327665)
          ·
            refine ⟨6958929741420076265495749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9278572988560101687327665 6958929741420076265495749)
            ·
              refine ⟨1304799326516264299780453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6958929741420076265495749 1304799326516264299780453)
              ·
                refine ⟨244649873721799556208835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1304799326516264299780453 244649873721799556208835)
                ·
                  refine ⟨366974810582699334313253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 244649873721799556208835 366974810582699334313253)
                  ·
                    refine ⟨68807776984256125183735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 366974810582699334313253 68807776984256125183735)
                    ·
                      rfl

theorem cell23_402008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 4, 1, 4].length) (baseStart_402008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402008 prefixEnd_402008 := by exact prefixLift 402008
  have htrace : WordTrace (prefixWord ++ tailWord_402008) baseStart_402008 baseEnd_402008 := by
    simpa [prefixWord, tailWord_402008, baseEnd_402008] using wordTrace_append hprefix tailTrace_402008
  have hstable : (prefixWord ++ tailWord_402008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402008).length < 2 ^ (prefixWord ++ tailWord_402008).sum := by decide
  have hdescent : baseEnd_402008 < baseStart_402008 := by decide
  rcases family_descends (prefixWord ++ tailWord_402008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402051 : List Nat := [1, 1, 1, 3, 3, 1, 4, 3, 1, 5]
def baseStart_402051 : Nat := 118140960795 + 402051 * 2 ^ 59
def prefixEnd_402051 : Nat := 4983230072969 + 3 ^ 40 * 402051 * 2
def baseEnd_402051 : Nat := 68815136873637235771169

theorem tailTrace_402051 : CollatzResearch.WordTrace tailWord_402051 prefixEnd_402051 68815136873637235771169 := by
  unfold tailWord_402051
  simp only [CollatzResearch.WordTrace]
  refine ⟨14664004666445366689222007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9776003110963577792814671 14664004666445366689222007)
  ·
    refine ⟨21996006999668050033833011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14664004666445366689222007 21996006999668050033833011)
    ·
      refine ⟨32994010499502075050749517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21996006999668050033833011 32994010499502075050749517)
      ·
        refine ⟨12372753937313278144031069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32994010499502075050749517 12372753937313278144031069)
        ·
          refine ⟨4639782726492479304011651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12372753937313278144031069 4639782726492479304011651)
          ·
            refine ⟨6959674089738718956017477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4639782726492479304011651 6959674089738718956017477)
            ·
              refine ⟨1304938891826009804253277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6959674089738718956017477 1304938891826009804253277)
              ·
                refine ⟨489352084434753676594979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1304938891826009804253277 489352084434753676594979)
                ·
                  refine ⟨734028126652130514892469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 489352084434753676594979 734028126652130514892469)
                  ·
                    refine ⟨68815136873637235771169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 734028126652130514892469 68815136873637235771169)
                    ·
                      rfl

theorem cell23_402051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3, 1, 5].length) (baseStart_402051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402051 prefixEnd_402051 := by exact prefixLift 402051
  have htrace : WordTrace (prefixWord ++ tailWord_402051) baseStart_402051 baseEnd_402051 := by
    simpa [prefixWord, tailWord_402051, baseEnd_402051] using wordTrace_append hprefix tailTrace_402051
  have hstable : (prefixWord ++ tailWord_402051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402051).length < 2 ^ (prefixWord ++ tailWord_402051).sum := by decide
  have hdescent : baseEnd_402051 < baseStart_402051 := by decide
  rcases family_descends (prefixWord ++ tailWord_402051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402071 : List Nat := [1, 1, 3, 3, 2, 1, 2, 2, 3, 1, 4]
def baseStart_402071 : Nat := 118140960795 + 402071 * 2 ^ 59
def prefixEnd_402071 : Nat := 4983230072969 + 3 ^ 40 * 402071 * 2
def baseEnd_402071 : Nat := 206455680234001629063415

theorem tailTrace_402071 : CollatzResearch.WordTrace tailWord_402071 prefixEnd_402071 206455680234001629063415 := by
  unfold tailWord_402071
  simp only [CollatzResearch.WordTrace]
  refine ⟨14664734126372910104950067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9776489417581940069966711 14664734126372910104950067)
  ·
    refine ⟨21997101189559365157425101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14664734126372910104950067 21997101189559365157425101)
    ·
      refine ⟨8248912946084761934034413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21997101189559365157425101 8248912946084761934034413)
      ·
        refine ⟨3093342354781785725262905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8248912946084761934034413 3093342354781785725262905)
        ·
          refine ⟨2320006766086339293947179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3093342354781785725262905 2320006766086339293947179)
          ·
            refine ⟨3480010149129508940920769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2320006766086339293947179 3480010149129508940920769)
            ·
              refine ⟨2610007611847131705690577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3480010149129508940920769 2610007611847131705690577)
              ·
                refine ⟨1957505708885348779267933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2610007611847131705690577 1957505708885348779267933)
                ·
                  refine ⟨734064640832005792225475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1957505708885348779267933 734064640832005792225475)
                  ·
                    refine ⟨1101096961248008688338213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 734064640832005792225475 1101096961248008688338213)
                    ·
                      refine ⟨206455680234001629063415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1101096961248008688338213 206455680234001629063415)
                      ·
                        rfl

theorem cell23_402071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_402071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402071 prefixEnd_402071 := by exact prefixLift 402071
  have htrace : WordTrace (prefixWord ++ tailWord_402071) baseStart_402071 baseEnd_402071 := by
    simpa [prefixWord, tailWord_402071, baseEnd_402071] using wordTrace_append hprefix tailTrace_402071
  have hstable : (prefixWord ++ tailWord_402071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402071).length < 2 ^ (prefixWord ++ tailWord_402071).sum := by decide
  have hdescent : baseEnd_402071 < baseStart_402071 := by decide
  rcases family_descends (prefixWord ++ tailWord_402071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402138 : List Nat := [3, 1, 1, 2, 2, 2, 4, 1, 1, 3, 3]
def baseStart_402138 : Nat := 118140960795 + 402138 * 2 ^ 59
def prefixEnd_402138 : Nat := 4983230072969 + 3 ^ 40 * 402138 * 2
def baseEnd_402138 : Nat := 206490083437852866925607

theorem tailTrace_402138 : CollatzResearch.WordTrace tailWord_402138 prefixEnd_402138 206490083437852866925607 := by
  unfold tailWord_402138
  simp only [CollatzResearch.WordTrace]
  refine ⟨3666794454282545136909767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9778118544753453698426045 3666794454282545136909767)
  ·
    refine ⟨5500191681423817705364651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3666794454282545136909767 5500191681423817705364651)
    ·
      refine ⟨8250287522135726558046977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5500191681423817705364651 8250287522135726558046977)
      ·
        refine ⟨6187715641601794918535233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8250287522135726558046977 6187715641601794918535233)
        ·
          refine ⟨4640786731201346188901425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6187715641601794918535233 4640786731201346188901425)
          ·
            refine ⟨3480590048401009641676069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4640786731201346188901425 3480590048401009641676069)
            ·
              refine ⟨652610634075189307814263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3480590048401009641676069 652610634075189307814263)
              ·
                refine ⟨978915951112783961721395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 652610634075189307814263 978915951112783961721395)
                ·
                  refine ⟨1468373926669175942582093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 978915951112783961721395 1468373926669175942582093)
                  ·
                    refine ⟨550640222500940978468285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1468373926669175942582093 550640222500940978468285)
                    ·
                      refine ⟨206490083437852866925607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 550640222500940978468285 206490083437852866925607)
                      ·
                        rfl

theorem cell23_402138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 1, 3, 3].length) (baseStart_402138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402138 prefixEnd_402138 := by exact prefixLift 402138
  have htrace : WordTrace (prefixWord ++ tailWord_402138) baseStart_402138 baseEnd_402138 := by
    simpa [prefixWord, tailWord_402138, baseEnd_402138] using wordTrace_append hprefix tailTrace_402138
  have hstable : (prefixWord ++ tailWord_402138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402138).length < 2 ^ (prefixWord ++ tailWord_402138).sum := by decide
  have hdescent : baseEnd_402138 < baseStart_402138 := by decide
  rcases family_descends (prefixWord ++ tailWord_402138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402172 : List Nat := [2, 2, 2, 1, 3, 4, 1, 2, 2, 1, 3]
def baseStart_402172 : Nat := 118140960795 + 402172 * 2 ^ 59
def prefixEnd_402172 : Nat := 4983230072969 + 3 ^ 40 * 402172 * 2
def baseEnd_402172 : Nat := 206507541780105733900451

theorem tailTrace_402172 : CollatzResearch.WordTrace tailWord_402172 prefixEnd_402172 206507541780105733900451 := by
  unfold tailWord_402172
  simp only [CollatzResearch.WordTrace]
  refine ⟨7334208949503502177188385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9778945266004669569584513 7334208949503502177188385)
  ·
    refine ⟨5500656712127626632891289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7334208949503502177188385 5500656712127626632891289)
    ·
      refine ⟨4125492534095719974668467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5500656712127626632891289 4125492534095719974668467)
      ·
        refine ⟨6188238801143579962002701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4125492534095719974668467 6188238801143579962002701)
        ·
          refine ⟨2320589550428842485751013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6188238801143579962002701 2320589550428842485751013)
          ·
            refine ⟨435110540705407966078315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2320589550428842485751013 435110540705407966078315)
            ·
              refine ⟨652665811058111949117473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 435110540705407966078315 652665811058111949117473)
              ·
                refine ⟨489499358293583961838105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 652665811058111949117473 489499358293583961838105)
                ·
                  refine ⟨367124518720187971378579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 489499358293583961838105 367124518720187971378579)
                  ·
                    refine ⟨550686778080281957067869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 367124518720187971378579 550686778080281957067869)
                    ·
                      refine ⟨206507541780105733900451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 550686778080281957067869 206507541780105733900451)
                      ·
                        rfl

theorem cell23_402172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 2, 2, 1, 3].length) (baseStart_402172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402172 prefixEnd_402172 := by exact prefixLift 402172
  have htrace : WordTrace (prefixWord ++ tailWord_402172) baseStart_402172 baseEnd_402172 := by
    simpa [prefixWord, tailWord_402172, baseEnd_402172] using wordTrace_append hprefix tailTrace_402172
  have hstable : (prefixWord ++ tailWord_402172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402172).length < 2 ^ (prefixWord ++ tailWord_402172).sum := by decide
  have hdescent : baseEnd_402172 < baseStart_402172 := by decide
  rcases family_descends (prefixWord ++ tailWord_402172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402181 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 1, 6, 3]
def baseStart_402181 : Nat := 118140960795 + 402181 * 2 ^ 59
def prefixEnd_402181 : Nat := 4983230072969 + 3 ^ 40 * 402181 * 2
def baseEnd_402181 : Nat := 206512163105996198687909

theorem tailTrace_402181 : CollatzResearch.WordTrace tailWord_402181 prefixEnd_402181 206512163105996198687909 := by
  unfold tailWord_402181
  simp only [CollatzResearch.WordTrace]
  refine ⟨14668746155974398891454397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9779164103982932594302931 14668746155974398891454397)
  ·
    refine ⟨5500779808490399584295399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14668746155974398891454397 5500779808490399584295399)
    ·
      refine ⟨8251169712735599376443099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5500779808490399584295399 8251169712735599376443099)
      ·
        refine ⟨12376754569103399064664649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8251169712735599376443099 12376754569103399064664649)
        ·
          refine ⟨9282565926827549298498487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12376754569103399064664649 9282565926827549298498487)
          ·
            refine ⟨13923848890241323947747731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9282565926827549298498487 13923848890241323947747731)
            ·
              refine ⟨20885773335361985921621597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13923848890241323947747731 20885773335361985921621597)
              ·
                refine ⟨7832165000760744720608099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20885773335361985921621597 7832165000760744720608099)
                ·
                  refine ⟨11748247501141117080912149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7832165000760744720608099 11748247501141117080912149)
                  ·
                    refine ⟨550699101615989863167757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11748247501141117080912149 550699101615989863167757)
                    ·
                      refine ⟨206512163105996198687909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 550699101615989863167757 206512163105996198687909)
                      ·
                        rfl

theorem cell23_402181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 6, 3].length) (baseStart_402181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402181 prefixEnd_402181 := by exact prefixLift 402181
  have htrace : WordTrace (prefixWord ++ tailWord_402181) baseStart_402181 baseEnd_402181 := by
    simpa [prefixWord, tailWord_402181, baseEnd_402181] using wordTrace_append hprefix tailTrace_402181
  have hstable : (prefixWord ++ tailWord_402181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402181).length < 2 ^ (prefixWord ++ tailWord_402181).sum := by decide
  have hdescent : baseEnd_402181 < baseStart_402181 := by decide
  rcases family_descends (prefixWord ++ tailWord_402181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402191 : List Nat := [1, 1, 2, 1, 1, 1, 5, 3, 2, 2, 4]
def baseStart_402191 : Nat := 118140960795 + 402191 * 2 ^ 59
def prefixEnd_402191 : Nat := 4983230072969 + 3 ^ 40 * 402191 * 2
def baseEnd_402191 : Nat := 206517297912541159562863

theorem tailTrace_402191 : CollatzResearch.WordTrace tailWord_402191 prefixEnd_402191 206517297912541159562863 := by
  unfold tailWord_402191
  simp only [CollatzResearch.WordTrace]
  refine ⟨14669110885938170599318427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9779407257292113732878951 14669110885938170599318427)
  ·
    refine ⟨22003666328907255898977641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14669110885938170599318427 22003666328907255898977641)
    ·
      refine ⟨16502749746680441924233231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22003666328907255898977641 16502749746680441924233231)
      ·
        refine ⟨24754124620020662886349847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16502749746680441924233231 24754124620020662886349847)
        ·
          refine ⟨37131186930030994329524771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24754124620020662886349847 37131186930030994329524771)
          ·
            refine ⟨55696780395046491494287157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37131186930030994329524771 55696780395046491494287157)
            ·
              refine ⟨5221573162035608577589421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55696780395046491494287157 5221573162035608577589421)
              ·
                refine ⟨1958089935763353216596033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5221573162035608577589421 1958089935763353216596033)
                ·
                  refine ⟨1468567451822514912447025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1958089935763353216596033 1468567451822514912447025)
                  ·
                    refine ⟨1101425588866886184335269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1468567451822514912447025 1101425588866886184335269)
                    ·
                      refine ⟨206517297912541159562863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1101425588866886184335269 206517297912541159562863)
                      ·
                        rfl

theorem cell23_402191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2, 4].length) (baseStart_402191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402191 prefixEnd_402191 := by exact prefixLift 402191
  have htrace : WordTrace (prefixWord ++ tailWord_402191) baseStart_402191 baseEnd_402191 := by
    simpa [prefixWord, tailWord_402191, baseEnd_402191] using wordTrace_append hprefix tailTrace_402191
  have hstable : (prefixWord ++ tailWord_402191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402191).length < 2 ^ (prefixWord ++ tailWord_402191).sum := by decide
  have hdescent : baseEnd_402191 < baseStart_402191 := by decide
  rcases family_descends (prefixWord ++ tailWord_402191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402285 : List Nat := [1, 5, 1, 1, 1, 1, 1, 4, 2, 4, 2]
def baseStart_402285 : Nat := 118140960795 + 402285 * 2 ^ 59
def prefixEnd_402285 : Nat := 4983230072969 + 3 ^ 40 * 402285 * 2
def baseEnd_402285 : Nat := 206565565094063791787431

theorem tailTrace_402285 : CollatzResearch.WordTrace tailWord_402285 prefixEnd_402285 206565565094063791787431 := by
  unfold tailWord_402285
  simp only [CollatzResearch.WordTrace]
  refine ⟨14672539347597624653240309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9781692898398416435493539 14672539347597624653240309)
  ·
    refine ⟨1375550563837277311241279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14672539347597624653240309 1375550563837277311241279)
    ·
      refine ⟨2063325845755915966861919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1375550563837277311241279 2063325845755915966861919)
      ·
        refine ⟨3094988768633873950292879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2063325845755915966861919 3094988768633873950292879)
        ·
          refine ⟨4642483152950810925439319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3094988768633873950292879 4642483152950810925439319)
          ·
            refine ⟨6963724729426216388158979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4642483152950810925439319 6963724729426216388158979)
            ·
              refine ⟨10445587094139324582238469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6963724729426216388158979 10445587094139324582238469)
              ·
                refine ⟨1958547580151123359169713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10445587094139324582238469 1958547580151123359169713)
                ·
                  refine ⟨1468910685113342519377285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1958547580151123359169713 1468910685113342519377285)
                  ·
                    refine ⟨275420753458751722383241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1468910685113342519377285 275420753458751722383241)
                    ·
                      refine ⟨206565565094063791787431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 275420753458751722383241 206565565094063791787431)
                      ·
                        rfl

theorem cell23_402285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 4, 2].length) (baseStart_402285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402285 prefixEnd_402285 := by exact prefixLift 402285
  have htrace : WordTrace (prefixWord ++ tailWord_402285) baseStart_402285 baseEnd_402285 := by
    simpa [prefixWord, tailWord_402285, baseEnd_402285] using wordTrace_append hprefix tailTrace_402285
  have hstable : (prefixWord ++ tailWord_402285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402285).length < 2 ^ (prefixWord ++ tailWord_402285).sum := by decide
  have hdescent : baseEnd_402285 < baseStart_402285 := by decide
  rcases family_descends (prefixWord ++ tailWord_402285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402286 : List Nat := [4, 1, 2, 3, 3, 1, 2, 2, 5]
def baseStart_402286 : Nat := 118140960795 + 402286 * 2 ^ 59
def prefixEnd_402286 : Nat := 4983230072969 + 3 ^ 40 * 402286 * 2
def baseEnd_402286 : Nat := 22951786508302031986103

theorem tailTrace_402286 : CollatzResearch.WordTrace tailWord_402286 prefixEnd_402286 22951786508302031986103 := by
  unfold tailWord_402286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1834071977574250228003339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9781717213729334549351141 1834071977574250228003339)
  ·
    refine ⟨2751107966361375342005009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1834071977574250228003339 2751107966361375342005009)
    ·
      refine ⟨2063330974771031506503757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2751107966361375342005009 2063330974771031506503757)
      ·
        refine ⟨773749115539136814938909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2063330974771031506503757 773749115539136814938909)
        ·
          refine ⟨290155918327176305602091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 773749115539136814938909 290155918327176305602091)
          ·
            refine ⟨435233877490764458403137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290155918327176305602091 435233877490764458403137)
            ·
              refine ⟨326425408118073343802353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 435233877490764458403137 326425408118073343802353)
              ·
                refine ⟨244819056088555007851765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 326425408118073343802353 244819056088555007851765)
                ·
                  refine ⟨22951786508302031986103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 244819056088555007851765 22951786508302031986103)
                  ·
                    rfl

theorem cell23_402286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 2, 5].length) (baseStart_402286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402286 prefixEnd_402286 := by exact prefixLift 402286
  have htrace : WordTrace (prefixWord ++ tailWord_402286) baseStart_402286 baseEnd_402286 := by
    simpa [prefixWord, tailWord_402286, baseEnd_402286] using wordTrace_append hprefix tailTrace_402286
  have hstable : (prefixWord ++ tailWord_402286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402286).length < 2 ^ (prefixWord ++ tailWord_402286).sum := by decide
  have hdescent : baseEnd_402286 < baseStart_402286 := by decide
  rcases family_descends (prefixWord ++ tailWord_402286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402291 : List Nat := [1, 1, 1, 2, 2, 1, 4, 3, 8]
def baseStart_402291 : Nat := 118140960795 + 402291 * 2 ^ 59
def prefixEnd_402291 : Nat := 4983230072969 + 3 ^ 40 * 402291 * 2
def baseEnd_402291 : Nat := 22952071775332307590267

theorem tailTrace_402291 : CollatzResearch.WordTrace tailWord_402291 prefixEnd_402291 22952071775332307590267 := by
  unfold tailWord_402291
  simp only [CollatzResearch.WordTrace]
  refine ⟨14672758185575887677958727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9781838790383925118639151 14672758185575887677958727)
  ·
    refine ⟨22009137278363831516938091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14672758185575887677958727 22009137278363831516938091)
    ·
      refine ⟨33013705917545747275407137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22009137278363831516938091 33013705917545747275407137)
      ·
        refine ⟨24760279438159310456555353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33013705917545747275407137 24760279438159310456555353)
        ·
          refine ⟨18570209578619482842416515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24760279438159310456555353 18570209578619482842416515)
          ·
            refine ⟨27855314367929224263624773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18570209578619482842416515 27855314367929224263624773)
            ·
              refine ⟨5222871443986729549429645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27855314367929224263624773 5222871443986729549429645)
              ·
                refine ⟨1958576791495023581036117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5222871443986729549429645 1958576791495023581036117)
                ·
                  refine ⟨22952071775332307590267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1958576791495023581036117 22952071775332307590267)
                  ·
                    rfl

theorem cell23_402291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 8].length) (baseStart_402291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402291 prefixEnd_402291 := by exact prefixLift 402291
  have htrace : WordTrace (prefixWord ++ tailWord_402291) baseStart_402291 baseEnd_402291 := by
    simpa [prefixWord, tailWord_402291, baseEnd_402291] using wordTrace_append hprefix tailTrace_402291
  have hstable : (prefixWord ++ tailWord_402291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402291).length < 2 ^ (prefixWord ++ tailWord_402291).sum := by decide
  have hdescent : baseEnd_402291 < baseStart_402291 := by decide
  rcases family_descends (prefixWord ++ tailWord_402291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402322 : List Nat := [3, 2, 3, 2, 2, 1, 1, 1, 1, 4, 3]
def baseStart_402322 : Nat := 118140960795 + 402322 * 2 ^ 59
def prefixEnd_402322 : Nat := 4983230072969 + 3 ^ 40 * 402322 * 2
def baseEnd_402322 : Nat := 206584563878280147024761

theorem tailTrace_402322 : CollatzResearch.WordTrace tailWord_402322 prefixEnd_402322 206584563878280147024761 := by
  unfold tailWord_402322
  simp only [CollatzResearch.WordTrace]
  refine ⟨3668472212115894993084305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9782592565642386648224813 3668472212115894993084305)
  ·
    refine ⟨2751354159086921244813229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3668472212115894993084305 2751354159086921244813229)
    ·
      refine ⟨1031757809657595466804961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2751354159086921244813229 1031757809657595466804961)
      ·
        refine ⟨773818357243196600103721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1031757809657595466804961 773818357243196600103721)
        ·
          refine ⟨580363767932397450077791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 773818357243196600103721 580363767932397450077791)
          ·
            refine ⟨870545651898596175116687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 580363767932397450077791 870545651898596175116687)
            ·
              refine ⟨1305818477847894262675031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 870545651898596175116687 1305818477847894262675031)
              ·
                refine ⟨1958727716771841394012547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1305818477847894262675031 1958727716771841394012547)
                ·
                  refine ⟨2938091575157762091018821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1958727716771841394012547 2938091575157762091018821)
                  ·
                    refine ⟨550892170342080392066029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2938091575157762091018821 550892170342080392066029)
                    ·
                      refine ⟨206584563878280147024761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 550892170342080392066029 206584563878280147024761)
                      ·
                        rfl

theorem cell23_402322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_402322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402322 prefixEnd_402322 := by exact prefixLift 402322
  have htrace : WordTrace (prefixWord ++ tailWord_402322) baseStart_402322 baseEnd_402322 := by
    simpa [prefixWord, tailWord_402322, baseEnd_402322] using wordTrace_append hprefix tailTrace_402322
  have hstable : (prefixWord ++ tailWord_402322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402322).length < 2 ^ (prefixWord ++ tailWord_402322).sum := by decide
  have hdescent : baseEnd_402322 < baseStart_402322 := by decide
  rcases family_descends (prefixWord ++ tailWord_402322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402345 : List Nat := [1, 2, 1, 1, 1, 1, 6, 1, 4, 3, 2]
def baseStart_402345 : Nat := 118140960795 + 402345 * 2 ^ 59
def prefixEnd_402345 : Nat := 4983230072969 + 3 ^ 40 * 402345 * 2
def baseEnd_402345 : Nat := 206596373933333557037155

theorem tailTrace_402345 : CollatzResearch.WordTrace tailWord_402345 prefixEnd_402345 206596373933333557037155 := by
  unfold tailWord_402345
  simp only [CollatzResearch.WordTrace]
  refine ⟨14674727727380254900424489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9783151818253503266949659 14674727727380254900424489)
  ·
    refine ⟨11006045795535191175318367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14674727727380254900424489 11006045795535191175318367)
    ·
      refine ⟨16509068693302786762977551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11006045795535191175318367 16509068693302786762977551)
      ·
        refine ⟨24763603039954180144466327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16509068693302786762977551 24763603039954180144466327)
        ·
          refine ⟨37145404559931270216699491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24763603039954180144466327 37145404559931270216699491)
          ·
            refine ⟨55718106839896905325049237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37145404559931270216699491 55718106839896905325049237)
            ·
              refine ⟨2611786258120167437111683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55718106839896905325049237 2611786258120167437111683)
              ·
                refine ⟨3917679387180251155667525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2611786258120167437111683 3917679387180251155667525)
                ·
                  refine ⟨734564885096297091687661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3917679387180251155667525 734564885096297091687661)
                  ·
                    refine ⟨275461831911111409382873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 734564885096297091687661 275461831911111409382873)
                    ·
                      refine ⟨206596373933333557037155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 275461831911111409382873 206596373933333557037155)
                      ·
                        rfl

theorem cell23_402345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4, 3, 2].length) (baseStart_402345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402345 prefixEnd_402345 := by exact prefixLift 402345
  have htrace : WordTrace (prefixWord ++ tailWord_402345) baseStart_402345 baseEnd_402345 := by
    simpa [prefixWord, tailWord_402345, baseEnd_402345] using wordTrace_append hprefix tailTrace_402345
  have hstable : (prefixWord ++ tailWord_402345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402345).length < 2 ^ (prefixWord ++ tailWord_402345).sum := by decide
  have hdescent : baseEnd_402345 < baseStart_402345 := by decide
  rcases family_descends (prefixWord ++ tailWord_402345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402375 : List Nat := [1, 1, 4, 1, 1, 2, 3, 4, 1, 1, 4]
def baseStart_402375 : Nat := 118140960795 + 402375 * 2 ^ 59
def prefixEnd_402375 : Nat := 4983230072969 + 3 ^ 40 * 402375 * 2
def baseEnd_402375 : Nat := 206611778352968439662017

theorem tailTrace_402375 : CollatzResearch.WordTrace tailWord_402375 prefixEnd_402375 206611778352968439662017 := by
  unfold tailWord_402375
  simp only [CollatzResearch.WordTrace]
  refine ⟨14675821917271570024016579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9783881278181046682677719 14675821917271570024016579)
  ·
    refine ⟨22013732875907355036024869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14675821917271570024016579 22013732875907355036024869)
    ·
      refine ⟨4127574914232629069254663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22013732875907355036024869 4127574914232629069254663)
      ·
        refine ⟨6191362371348943603881995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4127574914232629069254663 6191362371348943603881995)
        ·
          refine ⟨9287043557023415405822993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6191362371348943603881995 9287043557023415405822993)
          ·
            refine ⟨6965282667767561554367245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9287043557023415405822993 6965282667767561554367245)
            ·
              refine ⟨2611981000412835582887717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6965282667767561554367245 2611981000412835582887717)
              ·
                refine ⟨489746437577406671791447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2611981000412835582887717 489746437577406671791447)
                ·
                  refine ⟨734619656366110007687171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 489746437577406671791447 734619656366110007687171)
                  ·
                    refine ⟨1101929484549165011530757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 734619656366110007687171 1101929484549165011530757)
                    ·
                      refine ⟨206611778352968439662017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1101929484549165011530757 206611778352968439662017)
                      ·
                        rfl

theorem cell23_402375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4, 1, 1, 4].length) (baseStart_402375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402375 prefixEnd_402375 := by exact prefixLift 402375
  have htrace : WordTrace (prefixWord ++ tailWord_402375) baseStart_402375 baseEnd_402375 := by
    simpa [prefixWord, tailWord_402375, baseEnd_402375] using wordTrace_append hprefix tailTrace_402375
  have hstable : (prefixWord ++ tailWord_402375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402375).length < 2 ^ (prefixWord ++ tailWord_402375).sum := by decide
  have hdescent : baseEnd_402375 < baseStart_402375 := by decide
  rcases family_descends (prefixWord ++ tailWord_402375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402378 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 5, 1, 5]
def baseStart_402378 : Nat := 118140960795 + 402378 * 2 ^ 59
def prefixEnd_402378 : Nat := 4983230072969 + 3 ^ 40 * 402378 * 2
def baseEnd_402378 : Nat := 206613318794931927924503

theorem tailTrace_402378 : CollatzResearch.WordTrace tailWord_402378 prefixEnd_402378 206613318794931927924503 := by
  unfold tailWord_402378
  simp only [CollatzResearch.WordTrace]
  refine ⟨3668982834065175384093947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9783954224173801024250525 3668982834065175384093947)
  ·
    refine ⟨5503474251097763076140921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3668982834065175384093947 5503474251097763076140921)
    ·
      refine ⟨4127605688323322307105691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5503474251097763076140921 4127605688323322307105691)
      ·
        refine ⟨6191408532484983460658537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4127605688323322307105691 6191408532484983460658537)
        ·
          refine ⟨4643556399363737595493903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6191408532484983460658537 4643556399363737595493903)
          ·
            refine ⟨6965334599045606393240855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4643556399363737595493903 6965334599045606393240855)
            ·
              refine ⟨10448001898568409589861283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6965334599045606393240855 10448001898568409589861283)
              ·
                refine ⟨15672002847852614384791925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10448001898568409589861283 15672002847852614384791925)
                ·
                  refine ⟨1469250266986182598574243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15672002847852614384791925 1469250266986182598574243)
                  ·
                    refine ⟨2203875400479273897861365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1469250266986182598574243 2203875400479273897861365)
                    ·
                      refine ⟨206613318794931927924503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2203875400479273897861365 206613318794931927924503)
                      ·
                        rfl

theorem cell23_402378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_402378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402378 prefixEnd_402378 := by exact prefixLift 402378
  have htrace : WordTrace (prefixWord ++ tailWord_402378) baseStart_402378 baseEnd_402378 := by
    simpa [prefixWord, tailWord_402378, baseEnd_402378] using wordTrace_append hprefix tailTrace_402378
  have hstable : (prefixWord ++ tailWord_402378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402378).length < 2 ^ (prefixWord ++ tailWord_402378).sum := by decide
  have hdescent : baseEnd_402378 < baseStart_402378 := by decide
  rcases family_descends (prefixWord ++ tailWord_402378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402386 : List Nat := [3, 2, 2, 3, 1, 1, 3, 3, 1, 1, 3]
def baseStart_402386 : Nat := 118140960795 + 402386 * 2 ^ 59
def prefixEnd_402386 : Nat := 4983230072969 + 3 ^ 40 * 402386 * 2
def baseEnd_402386 : Nat := 206617426640167896624467

theorem tailTrace_402386 : CollatzResearch.WordTrace tailWord_402386 prefixEnd_402386 206617426640167896624467 := by
  unfold tailWord_402386
  simp only [CollatzResearch.WordTrace]
  refine ⟨3669055780057929725666753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9784148746821145935111341 3669055780057929725666753)
  ·
    refine ⟨2751791835043447294250065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3669055780057929725666753 2751791835043447294250065)
    ·
      refine ⟨2063843876282585470687549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2751791835043447294250065 2063843876282585470687549)
      ·
        refine ⟨773941453605969551507831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2063843876282585470687549 773941453605969551507831)
        ·
          refine ⟨1160912180408954327261747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 773941453605969551507831 1160912180408954327261747)
          ·
            refine ⟨1741368270613431490892621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1160912180408954327261747 1741368270613431490892621)
            ·
              refine ⟨653013101480036809084733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1741368270613431490892621 653013101480036809084733)
              ·
                refine ⟨244879913055013803406775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 653013101480036809084733 244879913055013803406775)
                ·
                  refine ⟨367319869582520705110163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 244879913055013803406775 367319869582520705110163)
                  ·
                    refine ⟨550979804373781057665245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 367319869582520705110163 550979804373781057665245)
                    ·
                      refine ⟨206617426640167896624467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 550979804373781057665245 206617426640167896624467)
                      ·
                        rfl

theorem cell23_402386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_402386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402386 prefixEnd_402386 := by exact prefixLift 402386
  have htrace : WordTrace (prefixWord ++ tailWord_402386) baseStart_402386 baseEnd_402386 := by
    simpa [prefixWord, tailWord_402386, baseEnd_402386] using wordTrace_append hprefix tailTrace_402386
  have hstable : (prefixWord ++ tailWord_402386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402386).length < 2 ^ (prefixWord ++ tailWord_402386).sum := by decide
  have hdescent : baseEnd_402386 < baseStart_402386 := by decide
  rcases family_descends (prefixWord ++ tailWord_402386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402425 : List Nat := [1, 2, 1, 3, 1, 3, 2, 3, 1, 3, 3]
def baseStart_402425 : Nat := 118140960795 + 402425 * 2 ^ 59
def prefixEnd_402425 : Nat := 4983230072969 + 3 ^ 40 * 402425 * 2
def baseEnd_402425 : Nat := 206637452385693244036787

theorem tailTrace_402425 : CollatzResearch.WordTrace tailWord_402425 prefixEnd_402425 206637452385693244036787 := by
  unfold tailWord_402425
  simp only [CollatzResearch.WordTrace]
  refine ⟨14677645567090428563336729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9785097044726952375557819 14677645567090428563336729)
  ·
    refine ⟨11008234175317821422502547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14677645567090428563336729 11008234175317821422502547)
    ·
      refine ⟨16512351262976732133753821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11008234175317821422502547 16512351262976732133753821)
      ·
        refine ⟨6192131723616274550157683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16512351262976732133753821 6192131723616274550157683)
        ·
          refine ⟨9288197585424411825236525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6192131723616274550157683 9288197585424411825236525)
          ·
            refine ⟨3483074094534154434463697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9288197585424411825236525 3483074094534154434463697)
            ·
              refine ⟨2612305570900615825847773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3483074094534154434463697 2612305570900615825847773)
              ·
                refine ⟨979614589087730934692915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2612305570900615825847773 979614589087730934692915)
                ·
                  refine ⟨1469421883631596402039373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 979614589087730934692915 1469421883631596402039373)
                  ·
                    refine ⟨551033206361848650764765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1469421883631596402039373 551033206361848650764765)
                    ·
                      refine ⟨206637452385693244036787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 551033206361848650764765 206637452385693244036787)
                      ·
                        rfl

theorem cell23_402425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 3, 3].length) (baseStart_402425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402425 prefixEnd_402425 := by exact prefixLift 402425
  have htrace : WordTrace (prefixWord ++ tailWord_402425) baseStart_402425 baseEnd_402425 := by
    simpa [prefixWord, tailWord_402425, baseEnd_402425] using wordTrace_append hprefix tailTrace_402425
  have hstable : (prefixWord ++ tailWord_402425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402425).length < 2 ^ (prefixWord ++ tailWord_402425).sum := by decide
  have hdescent : baseEnd_402425 < baseStart_402425 := by decide
  rcases family_descends (prefixWord ++ tailWord_402425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402442 : List Nat := [3, 1, 2, 2, 3, 2, 1, 2, 1, 3, 3]
def baseStart_402442 : Nat := 118140960795 + 402442 * 2 ^ 59
def prefixEnd_402442 : Nat := 4983230072969 + 3 ^ 40 * 402442 * 2
def baseEnd_402442 : Nat := 206646181556819677524209

theorem tailTrace_402442 : CollatzResearch.WordTrace tailWord_402442 prefixEnd_402442 206646181556819677524209 := by
  unfold tailWord_402442
  simp only [CollatzResearch.WordTrace]
  refine ⟨3669566402007210116676395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9785510405352560311137053 3669566402007210116676395)
  ·
    refine ⟨5504349603010815175014593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3669566402007210116676395 5504349603010815175014593)
    ·
      refine ⟨4128262202258111381260945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5504349603010815175014593 4128262202258111381260945)
      ·
        refine ⟨3096196651693583535945709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4128262202258111381260945 3096196651693583535945709)
        ·
          refine ⟨1161073744385093825979641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3096196651693583535945709 1161073744385093825979641)
          ·
            refine ⟨870805308288820369484731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1161073744385093825979641 870805308288820369484731)
            ·
              refine ⟨1306207962433230554227097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 870805308288820369484731 1306207962433230554227097)
              ·
                refine ⟨979655971824922915670323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1306207962433230554227097 979655971824922915670323)
                ·
                  refine ⟨1469483957737384373505485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 979655971824922915670323 1469483957737384373505485)
                  ·
                    refine ⟨551056484151519140064557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1469483957737384373505485 551056484151519140064557)
                    ·
                      refine ⟨206646181556819677524209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 551056484151519140064557 206646181556819677524209)
                      ·
                        rfl

theorem cell23_402442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_402442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402442 prefixEnd_402442 := by exact prefixLift 402442
  have htrace : WordTrace (prefixWord ++ tailWord_402442) baseStart_402442 baseEnd_402442 := by
    simpa [prefixWord, tailWord_402442, baseEnd_402442] using wordTrace_append hprefix tailTrace_402442
  have hstable : (prefixWord ++ tailWord_402442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402442).length < 2 ^ (prefixWord ++ tailWord_402442).sum := by decide
  have hdescent : baseEnd_402442 < baseStart_402442 := by decide
  rcases family_descends (prefixWord ++ tailWord_402442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402448 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 4]
def baseStart_402448 : Nat := 118140960795 + 402448 * 2 ^ 59
def prefixEnd_402448 : Nat := 4983230072969 + 3 ^ 40 * 402448 * 2
def baseEnd_402448 : Nat := 206649262440746654049181

theorem tailTrace_402448 : CollatzResearch.WordTrace tailWord_402448 prefixEnd_402448 206649262440746654049181 := by
  unfold tailWord_402448
  simp only [CollatzResearch.WordTrace]
  refine ⟨7339242223003551745711999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9785656297338068994282665 7339242223003551745711999)
  ·
    refine ⟨11008863334505327618567999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7339242223003551745711999 11008863334505327618567999)
    ·
      refine ⟨16513295001757991427851999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11008863334505327618567999 16513295001757991427851999)
      ·
        refine ⟨24769942502636987141777999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16513295001757991427851999 24769942502636987141777999)
        ·
          refine ⟨37154913753955480712666999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24769942502636987141777999 37154913753955480712666999)
          ·
            refine ⟨55732370630933221069000499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37154913753955480712666999 55732370630933221069000499)
            ·
              refine ⟨83598555946399831603500749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55732370630933221069000499 83598555946399831603500749)
              ·
                refine ⟨31349458479899936851312781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83598555946399831603500749 31349458479899936851312781)
                ·
                  refine ⟨11756046929962476319242293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31349458479899936851312781 11756046929962476319242293)
                  ·
                    refine ⟨1102129399683982154928965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11756046929962476319242293 1102129399683982154928965)
                    ·
                      refine ⟨206649262440746654049181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1102129399683982154928965 206649262440746654049181)
                      ·
                        rfl

theorem cell23_402448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 4].length) (baseStart_402448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402448 prefixEnd_402448 := by exact prefixLift 402448
  have htrace : WordTrace (prefixWord ++ tailWord_402448) baseStart_402448 baseEnd_402448 := by
    simpa [prefixWord, tailWord_402448, baseEnd_402448] using wordTrace_append hprefix tailTrace_402448
  have hstable : (prefixWord ++ tailWord_402448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402448).length < 2 ^ (prefixWord ++ tailWord_402448).sum := by decide
  have hdescent : baseEnd_402448 < baseStart_402448 := by decide
  rcases family_descends (prefixWord ++ tailWord_402448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402460 : List Nat := [2, 2, 3, 1, 4, 2, 2, 2, 1, 2, 2]
def baseStart_402460 : Nat := 118140960795 + 402460 * 2 ^ 59
def prefixEnd_402460 : Nat := 4983230072969 + 3 ^ 40 * 402460 * 2
def baseEnd_402460 : Nat := 206655424208600607099127

theorem tailTrace_402460 : CollatzResearch.WordTrace tailWord_402460 prefixEnd_402460 206655424208600607099127 := by
  unfold tailWord_402460
  simp only [CollatzResearch.WordTrace]
  refine ⟨7339461060981814770430417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9785948081309086360573889 7339461060981814770430417)
  ·
    refine ⟨5504595795736361077822813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7339461060981814770430417 5504595795736361077822813)
    ·
      refine ⟨2064223423401135404183555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5504595795736361077822813 2064223423401135404183555)
      ·
        refine ⟨3096335135101703106275333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2064223423401135404183555 3096335135101703106275333)
        ·
          refine ⟨580562837831569332426625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3096335135101703106275333 580562837831569332426625)
          ·
            refine ⟨435422128373676999319969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 580562837831569332426625 435422128373676999319969)
            ·
              refine ⟨326566596280257749489977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 435422128373676999319969 326566596280257749489977)
              ·
                refine ⟨244924947210193312117483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 326566596280257749489977 244924947210193312117483)
                ·
                  refine ⟨367387420815289968176225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 244924947210193312117483 367387420815289968176225)
                  ·
                    refine ⟨275540565611467476132169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 367387420815289968176225 275540565611467476132169)
                    ·
                      refine ⟨206655424208600607099127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 275540565611467476132169 206655424208600607099127)
                      ·
                        rfl

theorem cell23_402460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 2, 1, 2, 2].length) (baseStart_402460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402460 prefixEnd_402460 := by exact prefixLift 402460
  have htrace : WordTrace (prefixWord ++ tailWord_402460) baseStart_402460 baseEnd_402460 := by
    simpa [prefixWord, tailWord_402460, baseEnd_402460] using wordTrace_append hprefix tailTrace_402460
  have hstable : (prefixWord ++ tailWord_402460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402460).length < 2 ^ (prefixWord ++ tailWord_402460).sum := by decide
  have hdescent : baseEnd_402460 < baseStart_402460 := by decide
  rcases family_descends (prefixWord ++ tailWord_402460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402465 : List Nat := [1, 2, 3, 2, 3, 1, 1, 1, 2, 3, 4]
def baseStart_402465 : Nat := 118140960795 + 402465 * 2 ^ 59
def prefixEnd_402465 : Nat := 4983230072969 + 3 ^ 40 * 402465 * 2
def baseEnd_402465 : Nat := 206657991611873087536603

theorem tailTrace_402465 : CollatzResearch.WordTrace tailWord_402465 prefixEnd_402465 206657991611873087536603 := by
  unfold tailWord_402465
  simp only [CollatzResearch.WordTrace]
  refine ⟨14679104486945515394792849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9786069657963676929861899 14679104486945515394792849)
  ·
    refine ⟨11009328365209136546094637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14679104486945515394792849 11009328365209136546094637)
    ·
      refine ⟨4128498136953426204785489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11009328365209136546094637 4128498136953426204785489)
      ·
        refine ⟨3096373602715069653589117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4128498136953426204785489 3096373602715069653589117)
        ·
          refine ⟨1161140101018151120095919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3096373602715069653589117 1161140101018151120095919)
          ·
            refine ⟨1741710151527226680143879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1161140101018151120095919 1741710151527226680143879)
            ·
              refine ⟨2612565227290840020215819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1741710151527226680143879 2612565227290840020215819)
              ·
                refine ⟨3918847840936260030323729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2612565227290840020215819 3918847840936260030323729)
                ·
                  refine ⟨2939135880702195022742797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3918847840936260030323729 2939135880702195022742797)
                  ·
                    refine ⟨1102175955263323133528549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2939135880702195022742797 1102175955263323133528549)
                    ·
                      refine ⟨206657991611873087536603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1102175955263323133528549 206657991611873087536603)
                      ·
                        rfl

theorem cell23_402465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_402465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402465 prefixEnd_402465 := by exact prefixLift 402465
  have htrace : WordTrace (prefixWord ++ tailWord_402465) baseStart_402465 baseEnd_402465 := by
    simpa [prefixWord, tailWord_402465, baseEnd_402465] using wordTrace_append hprefix tailTrace_402465
  have hstable : (prefixWord ++ tailWord_402465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402465).length < 2 ^ (prefixWord ++ tailWord_402465).sum := by decide
  have hdescent : baseEnd_402465 < baseStart_402465 := by decide
  rcases family_descends (prefixWord ++ tailWord_402465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402485 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 4, 4, 3]
def baseStart_402485 : Nat := 118140960795 + 402485 * 2 ^ 59
def prefixEnd_402485 : Nat := 4983230072969 + 3 ^ 40 * 402485 * 2
def baseEnd_402485 : Nat := 206668261224963009286511

theorem tailTrace_402485 : CollatzResearch.WordTrace tailWord_402485 prefixEnd_402485 206668261224963009286511 := by
  unfold tailWord_402485
  simp only [CollatzResearch.WordTrace]
  refine ⟨14679833946873058810520909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9786555964582039207013939 14679833946873058810520909)
  ·
    refine ⟨5504937730077397053945341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14679833946873058810520909 5504937730077397053945341)
    ·
      refine ⟨2064351648779023895229503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5504937730077397053945341 2064351648779023895229503)
      ·
        refine ⟨3096527473168535842844255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2064351648779023895229503 3096527473168535842844255)
        ·
          refine ⟨4644791209752803764266383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3096527473168535842844255 4644791209752803764266383)
          ·
            refine ⟨6967186814629205646399575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4644791209752803764266383 6967186814629205646399575)
            ·
              refine ⟨10450780221943808469599363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6967186814629205646399575 10450780221943808469599363)
              ·
                refine ⟨15676170332915712704399045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10450780221943808469599363 15676170332915712704399045)
                ·
                  refine ⟨2939281937421696132074821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15676170332915712704399045 2939281937421696132074821)
                  ·
                    refine ⟨551115363266568024764029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2939281937421696132074821 551115363266568024764029)
                    ·
                      refine ⟨206668261224963009286511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 551115363266568024764029 206668261224963009286511)
                      ·
                        rfl

theorem cell23_402485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_402485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402485 prefixEnd_402485 := by exact prefixLift 402485
  have htrace : WordTrace (prefixWord ++ tailWord_402485) baseStart_402485 baseEnd_402485 := by
    simpa [prefixWord, tailWord_402485, baseEnd_402485] using wordTrace_append hprefix tailTrace_402485
  have hstable : (prefixWord ++ tailWord_402485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402485).length < 2 ^ (prefixWord ++ tailWord_402485).sum := by decide
  have hdescent : baseEnd_402485 < baseStart_402485 := by decide
  rcases family_descends (prefixWord ++ tailWord_402485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402515 : List Nat := [1, 1, 1, 2, 1, 1, 2, 6, 2, 3, 3]
def baseStart_402515 : Nat := 118140960795 + 402515 * 2 ^ 59
def prefixEnd_402515 : Nat := 4983230072969 + 3 ^ 40 * 402515 * 2
def baseEnd_402515 : Nat := 206683665644597891911373

theorem tailTrace_402515 : CollatzResearch.WordTrace tailWord_402515 prefixEnd_402515 206683665644597891911373 := by
  unfold tailWord_402515
  simp only [CollatzResearch.WordTrace]
  refine ⟨14680928136764373934112999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9787285424509582622741999 14680928136764373934112999)
  ·
    refine ⟨22021392205146560901169499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14680928136764373934112999 22021392205146560901169499)
    ·
      refine ⟨33032088307719841351754249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22021392205146560901169499 33032088307719841351754249)
      ·
        refine ⟨24774066230789881013815687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33032088307719841351754249 24774066230789881013815687)
        ·
          refine ⟨37161099346184821520723531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24774066230789881013815687 37161099346184821520723531)
          ·
            refine ⟨55741649019277232281085297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37161099346184821520723531 55741649019277232281085297)
            ·
              refine ⟨41806236764457924210813973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55741649019277232281085297 41806236764457924210813973)
              ·
                refine ⟨1959667348333965197381905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41806236764457924210813973 1959667348333965197381905)
                ·
                  refine ⟨1469750511250473898036429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1959667348333965197381905 1469750511250473898036429)
                  ·
                    refine ⟨551156441718927711763661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1469750511250473898036429 551156441718927711763661)
                    ·
                      refine ⟨206683665644597891911373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 551156441718927711763661 206683665644597891911373)
                      ·
                        rfl

theorem cell23_402515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 3, 3].length) (baseStart_402515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402515 prefixEnd_402515 := by exact prefixLift 402515
  have htrace : WordTrace (prefixWord ++ tailWord_402515) baseStart_402515 baseEnd_402515 := by
    simpa [prefixWord, tailWord_402515, baseEnd_402515] using wordTrace_append hprefix tailTrace_402515
  have hstable : (prefixWord ++ tailWord_402515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402515).length < 2 ^ (prefixWord ++ tailWord_402515).sum := by decide
  have hdescent : baseEnd_402515 < baseStart_402515 := by decide
  rcases family_descends (prefixWord ++ tailWord_402515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402516 : List Nat := [2, 4, 1, 1, 1, 1, 5, 2, 2, 2, 2]
def baseStart_402516 : Nat := 118140960795 + 402516 * 2 ^ 59
def prefixEnd_402516 : Nat := 4983230072969 + 3 ^ 40 * 402516 * 2
def baseEnd_402516 : Nat := 206684179125252387998869

theorem tailTrace_402516 : CollatzResearch.WordTrace tailWord_402516 prefixEnd_402516 206684179125252387998869 := by
  unfold tailWord_402516
  simp only [CollatzResearch.WordTrace]
  refine ⟨7340482304880375552449701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9787309739840500736599601 7340482304880375552449701)
  ·
    refine ⟨1376340432165070416084319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7340482304880375552449701 1376340432165070416084319)
    ·
      refine ⟨2064510648247605624126479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1376340432165070416084319 2064510648247605624126479)
      ·
        refine ⟨3096765972371408436189719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2064510648247605624126479 3096765972371408436189719)
        ·
          refine ⟨4645148958557112654284579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3096765972371408436189719 4645148958557112654284579)
          ·
            refine ⟨6967723437835668981426869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4645148958557112654284579 6967723437835668981426869)
            ·
              refine ⟨653224072297093967008769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6967723437835668981426869 653224072297093967008769)
              ·
                refine ⟨489918054222820475256577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 653224072297093967008769 489918054222820475256577)
                ·
                  refine ⟨367438540667115356442433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 489918054222820475256577 367438540667115356442433)
                  ·
                    refine ⟨275578905500336517331825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 367438540667115356442433 275578905500336517331825)
                    ·
                      refine ⟨206684179125252387998869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 275578905500336517331825 206684179125252387998869)
                      ·
                        rfl

theorem cell23_402516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2, 2, 2, 2].length) (baseStart_402516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402516 prefixEnd_402516 := by exact prefixLift 402516
  have htrace : WordTrace (prefixWord ++ tailWord_402516) baseStart_402516 baseEnd_402516 := by
    simpa [prefixWord, tailWord_402516, baseEnd_402516] using wordTrace_append hprefix tailTrace_402516
  have hstable : (prefixWord ++ tailWord_402516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402516).length < 2 ^ (prefixWord ++ tailWord_402516).sum := by decide
  have hdescent : baseEnd_402516 < baseStart_402516 := by decide
  rcases family_descends (prefixWord ++ tailWord_402516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402535 : List Nat := [1, 1, 5, 1, 1, 3, 1, 2, 1, 7]
def baseStart_402535 : Nat := 118140960795 + 402535 * 2 ^ 59
def prefixEnd_402535 : Nat := 4983230072969 + 3 ^ 40 * 402535 * 2
def baseEnd_402535 : Nat := 68897978419229271220427

theorem tailTrace_402535 : CollatzResearch.WordTrace tailWord_402535 prefixEnd_402535 68897978419229271220427 := by
  unfold tailWord_402535
  simp only [CollatzResearch.WordTrace]
  refine ⟨14681657596691917349841059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9787771731127944899894039 14681657596691917349841059)
  ·
    refine ⟨22022486395037876024761589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14681657596691917349841059 22022486395037876024761589)
    ·
      refine ⟨2064608099534800877321399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22022486395037876024761589 2064608099534800877321399)
      ·
        refine ⟨3096912149302201315982099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2064608099534800877321399 3096912149302201315982099)
        ·
          refine ⟨4645368223953301973973149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3096912149302201315982099 4645368223953301973973149)
          ·
            refine ⟨1742013083982488240239931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4645368223953301973973149 1742013083982488240239931)
            ·
              refine ⟨2613019625973732360359897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1742013083982488240239931 2613019625973732360359897)
              ·
                refine ⟨1959764719480299270269923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2613019625973732360359897 1959764719480299270269923)
                ·
                  refine ⟨2939647079220448905404885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1959764719480299270269923 2939647079220448905404885)
                  ·
                    refine ⟨68897978419229271220427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2939647079220448905404885 68897978419229271220427)
                    ·
                      rfl

theorem cell23_402535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_402535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402535 prefixEnd_402535 := by exact prefixLift 402535
  have htrace : WordTrace (prefixWord ++ tailWord_402535) baseStart_402535 baseEnd_402535 := by
    simpa [prefixWord, tailWord_402535, baseEnd_402535] using wordTrace_append hprefix tailTrace_402535
  have hstable : (prefixWord ++ tailWord_402535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402535).length < 2 ^ (prefixWord ++ tailWord_402535).sum := by decide
  have hdescent : baseEnd_402535 < baseStart_402535 := by decide
  rcases family_descends (prefixWord ++ tailWord_402535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402555 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 6, 1, 4]
def baseStart_402555 : Nat := 118140960795 + 402555 * 2 ^ 59
def prefixEnd_402555 : Nat := 4983230072969 + 3 ^ 40 * 402555 * 2
def baseEnd_402555 : Nat := 206704204870777735411189

theorem tailTrace_402555 : CollatzResearch.WordTrace tailWord_402555 prefixEnd_402555 206704204870777735411189 := by
  unfold tailWord_402555
  simp only [CollatzResearch.WordTrace]
  refine ⟨14682387056619460765569119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9788258037746307177046079 14682387056619460765569119)
  ·
    refine ⟨22023580584929191148353679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14682387056619460765569119 22023580584929191148353679)
    ·
      refine ⟨33035370877393786722530519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22023580584929191148353679 33035370877393786722530519)
      ·
        refine ⟨49553056316090680083795779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33035370877393786722530519 49553056316090680083795779)
        ·
          refine ⟨74329584474136020125693669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49553056316090680083795779 74329584474136020125693669)
          ·
            refine ⟨13936797088900503773567563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74329584474136020125693669 13936797088900503773567563)
            ·
              refine ⟨20905195633350755660351345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13936797088900503773567563 20905195633350755660351345)
              ·
                refine ⟨15678896725013066745263509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20905195633350755660351345 15678896725013066745263509)
                ·
                  refine ⟨734948283984987503684227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15678896725013066745263509 734948283984987503684227)
                  ·
                    refine ⟨1102422425977481255526341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 734948283984987503684227 1102422425977481255526341)
                    ·
                      refine ⟨206704204870777735411189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1102422425977481255526341 206704204870777735411189)
                      ·
                        rfl

theorem cell23_402555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6, 1, 4].length) (baseStart_402555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402555 prefixEnd_402555 := by exact prefixLift 402555
  have htrace : WordTrace (prefixWord ++ tailWord_402555) baseStart_402555 baseEnd_402555 := by
    simpa [prefixWord, tailWord_402555, baseEnd_402555] using wordTrace_append hprefix tailTrace_402555
  have hstable : (prefixWord ++ tailWord_402555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402555).length < 2 ^ (prefixWord ++ tailWord_402555).sum := by decide
  have hdescent : baseEnd_402555 < baseStart_402555 := by decide
  rcases family_descends (prefixWord ++ tailWord_402555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402572 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 4, 4, 2]
def baseStart_402572 : Nat := 118140960795 + 402572 * 2 ^ 59
def prefixEnd_402572 : Nat := 4983230072969 + 3 ^ 40 * 402572 * 2
def baseEnd_402572 : Nat := 206712934041904168898611

theorem tailTrace_402572 : CollatzResearch.WordTrace tailWord_402572 prefixEnd_402572 206712934041904168898611 := by
  unfold tailWord_402572
  simp only [CollatzResearch.WordTrace]
  refine ⟨7341503548778936334468985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9788671398371915112625313 7341503548778936334468985)
  ·
    refine ⟨5506127661584202250851739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7341503548778936334468985 5506127661584202250851739)
    ·
      refine ⟨8259191492376303376277609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5506127661584202250851739 8259191492376303376277609)
      ·
        refine ⟨6194393619282227532208207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8259191492376303376277609 6194393619282227532208207)
        ·
          refine ⟨9291590428923341298312311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6194393619282227532208207 9291590428923341298312311)
          ·
            refine ⟨13937385643385011947468467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9291590428923341298312311 13937385643385011947468467)
            ·
              refine ⟨20906078465077517921202701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13937385643385011947468467 20906078465077517921202701)
              ·
                refine ⟨7839779424404069220451013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20906078465077517921202701 7839779424404069220451013)
                ·
                  refine ⟨1469958642075762978834565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7839779424404069220451013 1469958642075762978834565)
                  ·
                    refine ⟨275617245389205558531481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1469958642075762978834565 275617245389205558531481)
                    ·
                      refine ⟨206712934041904168898611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 275617245389205558531481 206712934041904168898611)
                      ·
                        rfl

theorem cell23_402572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 4, 4, 2].length) (baseStart_402572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402572 prefixEnd_402572 := by exact prefixLift 402572
  have htrace : WordTrace (prefixWord ++ tailWord_402572) baseStart_402572 baseEnd_402572 := by
    simpa [prefixWord, tailWord_402572, baseEnd_402572] using wordTrace_append hprefix tailTrace_402572
  have hstable : (prefixWord ++ tailWord_402572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402572).length < 2 ^ (prefixWord ++ tailWord_402572).sum := by decide
  have hdescent : baseEnd_402572 < baseStart_402572 := by decide
  rcases family_descends (prefixWord ++ tailWord_402572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402592 : List Nat := [2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 3]
def baseStart_402592 : Nat := 118140960795 + 402592 * 2 ^ 59
def prefixEnd_402592 : Nat := 4983230072969 + 3 ^ 40 * 402592 * 2
def baseEnd_402592 : Nat := 206723203654994090648519

theorem tailTrace_402592 : CollatzResearch.WordTrace tailWord_402592 prefixEnd_402592 206723203654994090648519 := by
  unfold tailWord_402592
  simp only [CollatzResearch.WordTrace]
  refine ⟨7341868278742708042333015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9789157704990277389777353 7341868278742708042333015)
  ·
    refine ⟨11012802418114062063499523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7341868278742708042333015 11012802418114062063499523)
    ·
      refine ⟨16519203627171093095249285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11012802418114062063499523 16519203627171093095249285)
      ·
        refine ⟨3097350680094579955359241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16519203627171093095249285 3097350680094579955359241)
        ·
          refine ⟨2323013010070934966519431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3097350680094579955359241 2323013010070934966519431)
          ·
            refine ⟨3484519515106402449779147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2323013010070934966519431 3484519515106402449779147)
            ·
              refine ⟨5226779272659603674668721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3484519515106402449779147 5226779272659603674668721)
              ·
                refine ⟨3920084454494702756001541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5226779272659603674668721 3920084454494702756001541)
                ·
                  refine ⟨735015835217756766750289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3920084454494702756001541 735015835217756766750289)
                  ·
                    refine ⟨551261876413317575062717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 735015835217756766750289 551261876413317575062717)
                    ·
                      refine ⟨206723203654994090648519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 551261876413317575062717 206723203654994090648519)
                      ·
                        rfl

theorem cell23_402592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_402592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402592 prefixEnd_402592 := by exact prefixLift 402592
  have htrace : WordTrace (prefixWord ++ tailWord_402592) baseStart_402592 baseEnd_402592 := by
    simpa [prefixWord, tailWord_402592, baseEnd_402592] using wordTrace_append hprefix tailTrace_402592
  have hstable : (prefixWord ++ tailWord_402592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402592).length < 2 ^ (prefixWord ++ tailWord_402592).sum := by decide
  have hdescent : baseEnd_402592 < baseStart_402592 := by decide
  rcases family_descends (prefixWord ++ tailWord_402592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402609 : List Nat := [1, 2, 2, 5, 1, 1, 1, 3, 2, 2, 3]
def baseStart_402609 : Nat := 118140960795 + 402609 * 2 ^ 59
def prefixEnd_402609 : Nat := 4983230072969 + 3 ^ 40 * 402609 * 2
def baseEnd_402609 : Nat := 206731932826120524135941

theorem tailTrace_402609 : CollatzResearch.WordTrace tailWord_402609 prefixEnd_402609 206731932826120524135941 := by
  unfold tailWord_402609
  simp only [CollatzResearch.WordTrace]
  refine ⟨14684356598423827988034881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9789571065615885325356587 14684356598423827988034881)
  ·
    refine ⟨11013267448817870991026161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14684356598423827988034881 11013267448817870991026161)
    ·
      refine ⟨8259950586613403243269621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11013267448817870991026161 8259950586613403243269621)
      ·
        refine ⟨774370367495006554056527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8259950586613403243269621 774370367495006554056527)
        ·
          refine ⟨1161555551242509831084791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 774370367495006554056527 1161555551242509831084791)
          ·
            refine ⟨1742333326863764746627187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1161555551242509831084791 1742333326863764746627187)
            ·
              refine ⟨2613499990295647119940781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1742333326863764746627187 2613499990295647119940781)
              ·
                refine ⟨980062496360867669977793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2613499990295647119940781 980062496360867669977793)
                ·
                  refine ⟨735046872270650752483345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 980062496360867669977793 735046872270650752483345)
                  ·
                    refine ⟨551285154202988064362509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 735046872270650752483345 551285154202988064362509)
                    ·
                      refine ⟨206731932826120524135941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 551285154202988064362509 206731932826120524135941)
                      ·
                        rfl

theorem cell23_402609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_402609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402609 prefixEnd_402609 := by exact prefixLift 402609
  have htrace : WordTrace (prefixWord ++ tailWord_402609) baseStart_402609 baseEnd_402609 := by
    simpa [prefixWord, tailWord_402609, baseEnd_402609] using wordTrace_append hprefix tailTrace_402609
  have hstable : (prefixWord ++ tailWord_402609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402609).length < 2 ^ (prefixWord ++ tailWord_402609).sum := by decide
  have hdescent : baseEnd_402609 < baseStart_402609 := by decide
  rcases family_descends (prefixWord ++ tailWord_402609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402642 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 5, 5]
def baseStart_402642 : Nat := 118140960795 + 402642 * 2 ^ 59
def prefixEnd_402642 : Nat := 4983230072969 + 3 ^ 40 * 402642 * 2
def baseEnd_402642 : Nat := 68916292562572965007763

theorem tailTrace_402642 : CollatzResearch.WordTrace tailWord_402642 prefixEnd_402642 68916292562572965007763 := by
  unfold tailWord_402642
  simp only [CollatzResearch.WordTrace]
  refine ⟨3671390051826068655996545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9790373471536183082657453 3671390051826068655996545)
  ·
    refine ⟨2753542538869551491997409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3671390051826068655996545 2753542538869551491997409)
    ·
      refine ⟨2065156904152163618998057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2753542538869551491997409 2065156904152163618998057)
      ·
        refine ⟨1548867678114122714248543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2065156904152163618998057 1548867678114122714248543)
        ·
          refine ⟨2323301517171184071372815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1548867678114122714248543 2323301517171184071372815)
          ·
            refine ⟨3484952275756776107059223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2323301517171184071372815 3484952275756776107059223)
            ·
              refine ⟨5227428413635164160588835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3484952275756776107059223 5227428413635164160588835)
              ·
                refine ⟨7841142620452746240883253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5227428413635164160588835 7841142620452746240883253)
                ·
                  refine ⟨735107120667444960082805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7841142620452746240883253 735107120667444960082805)
                  ·
                    refine ⟨68916292562572965007763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 735107120667444960082805 68916292562572965007763)
                    ·
                      rfl

theorem cell23_402642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_402642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402642 prefixEnd_402642 := by exact prefixLift 402642
  have htrace : WordTrace (prefixWord ++ tailWord_402642) baseStart_402642 baseEnd_402642 := by
    simpa [prefixWord, tailWord_402642, baseEnd_402642] using wordTrace_append hprefix tailTrace_402642
  have hstable : (prefixWord ++ tailWord_402642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402642).length < 2 ^ (prefixWord ++ tailWord_402642).sum := by decide
  have hdescent : baseEnd_402642 < baseStart_402642 := by decide
  rcases family_descends (prefixWord ++ tailWord_402642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402665 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 2, 5, 5]
def baseStart_402665 : Nat := 118140960795 + 402665 * 2 ^ 59
def prefixEnd_402665 : Nat := 4983230072969 + 3 ^ 40 * 402665 * 2
def baseEnd_402665 : Nat := 206760687742772305035683

theorem tailTrace_402665 : CollatzResearch.WordTrace tailWord_402665 prefixEnd_402665 206760687742772305035683 := by
  unfold tailWord_402665
  simp only [CollatzResearch.WordTrace]
  refine ⟨14686399086220949552073449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9790932724147299701382299 14686399086220949552073449)
  ·
    refine ⟨11014799314665712164055087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14686399086220949552073449 11014799314665712164055087)
    ·
      refine ⟨16522198971998568246082631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11014799314665712164055087 16522198971998568246082631)
      ·
        refine ⟨24783298457997852369123947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16522198971998568246082631 24783298457997852369123947)
        ·
          refine ⟨37174947686996778553685921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24783298457997852369123947 37174947686996778553685921)
          ·
            refine ⟨27881210765247583915264441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37174947686996778553685921 27881210765247583915264441)
            ·
              refine ⟨20910908073935687936448331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27881210765247583915264441 20910908073935687936448331)
              ·
                refine ⟨31366362110903531904672497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20910908073935687936448331 31366362110903531904672497)
                ·
                  refine ⟨23524771583177648928504373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31366362110903531904672497 23524771583177648928504373)
                  ·
                    refine ⟨2205447335922904587047285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23524771583177648928504373 2205447335922904587047285)
                    ·
                      refine ⟨206760687742772305035683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2205447335922904587047285 206760687742772305035683)
                      ·
                        rfl

theorem cell23_402665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 5, 5].length) (baseStart_402665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402665 prefixEnd_402665 := by exact prefixLift 402665
  have htrace : WordTrace (prefixWord ++ tailWord_402665) baseStart_402665 baseEnd_402665 := by
    simpa [prefixWord, tailWord_402665, baseEnd_402665] using wordTrace_append hprefix tailTrace_402665
  have hstable : (prefixWord ++ tailWord_402665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402665).length < 2 ^ (prefixWord ++ tailWord_402665).sum := by decide
  have hdescent : baseEnd_402665 < baseStart_402665 := by decide
  rcases family_descends (prefixWord ++ tailWord_402665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402666 : List Nat := [3, 1, 3, 1, 1, 3, 3, 1, 2, 3, 2]
def baseStart_402666 : Nat := 118140960795 + 402666 * 2 ^ 59
def prefixEnd_402666 : Nat := 4983230072969 + 3 ^ 40 * 402666 * 2
def baseEnd_402666 : Nat := 206761201223426801123179

theorem tailTrace_402666 : CollatzResearch.WordTrace tailWord_402666 prefixEnd_402666 206761201223426801123179 := by
  unfold tailWord_402666
  simp only [CollatzResearch.WordTrace]
  refine ⟨3671608889804331680714963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9790957039478217815239901 3671608889804331680714963)
  ·
    refine ⟨5507413334706497521072445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3671608889804331680714963 5507413334706497521072445)
    ·
      refine ⟨2065280000514936570402167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5507413334706497521072445 2065280000514936570402167)
      ·
        refine ⟨3097920000772404855603251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2065280000514936570402167 3097920000772404855603251)
        ·
          refine ⟨4646880001158607283404877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3097920000772404855603251 4646880001158607283404877)
          ·
            refine ⟨1742580000434477731276829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4646880001158607283404877 1742580000434477731276829)
            ·
              refine ⟨653467500162929149228811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1742580000434477731276829 653467500162929149228811)
              ·
                refine ⟨980201250244393723843217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 653467500162929149228811 980201250244393723843217)
                ·
                  refine ⟨735150937683295292882413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 980201250244393723843217 735150937683295292882413)
                  ·
                    refine ⟨275681601631235734830905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 735150937683295292882413 275681601631235734830905)
                    ·
                      refine ⟨206761201223426801123179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 275681601631235734830905 206761201223426801123179)
                      ·
                        rfl

theorem cell23_402666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 2, 3, 2].length) (baseStart_402666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402666 prefixEnd_402666 := by exact prefixLift 402666
  have htrace : WordTrace (prefixWord ++ tailWord_402666) baseStart_402666 baseEnd_402666 := by
    simpa [prefixWord, tailWord_402666, baseEnd_402666] using wordTrace_append hprefix tailTrace_402666
  have hstable : (prefixWord ++ tailWord_402666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402666).length < 2 ^ (prefixWord ++ tailWord_402666).sum := by decide
  have hdescent : baseEnd_402666 < baseStart_402666 := by decide
  rcases family_descends (prefixWord ++ tailWord_402666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402682 : List Nat := [3, 1, 1, 1, 1, 4, 2, 3, 1, 1, 5]
def baseStart_402682 : Nat := 118140960795 + 402682 * 2 ^ 59
def prefixEnd_402682 : Nat := 4983230072969 + 3 ^ 40 * 402682 * 2
def baseEnd_402682 : Nat := 206769416913898738523105

theorem tailTrace_402682 : CollatzResearch.WordTrace tailWord_402682 prefixEnd_402682 206769416913898738523105 := by
  unfold tailWord_402682
  simp only [CollatzResearch.WordTrace]
  refine ⟨3671754781789840363860575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9791346084772907636961533 3671754781789840363860575)
  ·
    refine ⟨5507632172684760545790863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3671754781789840363860575 5507632172684760545790863)
    ·
      refine ⟨8261448259027140818686295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5507632172684760545790863 8261448259027140818686295)
      ·
        refine ⟨12392172388540711228029443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8261448259027140818686295 12392172388540711228029443)
        ·
          refine ⟨18588258582811066842044165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12392172388540711228029443 18588258582811066842044165)
          ·
            refine ⟨3485298484277075032883281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18588258582811066842044165 3485298484277075032883281)
            ·
              refine ⟨2613973863207806274662461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3485298484277075032883281 2613973863207806274662461)
              ·
                refine ⟨980240198702927352998423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2613973863207806274662461 980240198702927352998423)
                ·
                  refine ⟨1470360298054391029497635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 980240198702927352998423 1470360298054391029497635)
                  ·
                    refine ⟨2205540447081586544246453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1470360298054391029497635 2205540447081586544246453)
                    ·
                      refine ⟨206769416913898738523105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2205540447081586544246453 206769416913898738523105)
                      ·
                        rfl

theorem cell23_402682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 1, 1, 5].length) (baseStart_402682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402682 prefixEnd_402682 := by exact prefixLift 402682
  have htrace : WordTrace (prefixWord ++ tailWord_402682) baseStart_402682 baseEnd_402682 := by
    simpa [prefixWord, tailWord_402682, baseEnd_402682] using wordTrace_append hprefix tailTrace_402682
  have hstable : (prefixWord ++ tailWord_402682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402682).length < 2 ^ (prefixWord ++ tailWord_402682).sum := by decide
  have hdescent : baseEnd_402682 < baseStart_402682 := by decide
  rcases family_descends (prefixWord ++ tailWord_402682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402689 : List Nat := [1, 2, 4, 1, 1, 4, 1, 1, 4, 4]
def baseStart_402689 : Nat := 118140960795 + 402689 * 2 ^ 59
def prefixEnd_402689 : Nat := 4983230072969 + 3 ^ 40 * 402689 * 2
def baseEnd_402689 : Nat := 68924337092826737045191

theorem tailTrace_402689 : CollatzResearch.WordTrace tailWord_402689 prefixEnd_402689 68924337092826737045191 := by
  unfold tailWord_402689
  simp only [CollatzResearch.WordTrace]
  refine ⟨14687274438134001650947121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9791516292089334433964747 14687274438134001650947121)
  ·
    refine ⟨11015455828600501238210341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14687274438134001650947121 11015455828600501238210341)
    ·
      refine ⟨2065397967862593982164439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11015455828600501238210341 2065397967862593982164439)
      ·
        refine ⟨3098096951793890973246659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2065397967862593982164439 3098096951793890973246659)
        ·
          refine ⟨4647145427690836459869989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3098096951793890973246659 4647145427690836459869989)
          ·
            refine ⟨871339767692031836225623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4647145427690836459869989 871339767692031836225623)
            ·
              refine ⟨1307009651538047754338435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 871339767692031836225623 1307009651538047754338435)
              ·
                refine ⟨1960514477307071631507653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1307009651538047754338435 1960514477307071631507653)
                ·
                  refine ⟨367596464495075930907685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1960514477307071631507653 367596464495075930907685)
                  ·
                    refine ⟨68924337092826737045191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 367596464495075930907685 68924337092826737045191)
                    ·
                      rfl

theorem cell23_402689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_402689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402689 prefixEnd_402689 := by exact prefixLift 402689
  have htrace : WordTrace (prefixWord ++ tailWord_402689) baseStart_402689 baseEnd_402689 := by
    simpa [prefixWord, tailWord_402689, baseEnd_402689] using wordTrace_append hprefix tailTrace_402689
  have hstable : (prefixWord ++ tailWord_402689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402689).length < 2 ^ (prefixWord ++ tailWord_402689).sum := by decide
  have hdescent : baseEnd_402689 < baseStart_402689 := by decide
  rcases family_descends (prefixWord ++ tailWord_402689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402733 : List Nat := [1, 5, 3, 1, 1, 1, 2, 3, 1, 2, 3]
def baseStart_402733 : Nat := 118140960795 + 402733 * 2 ^ 59
def prefixEnd_402733 : Nat := 4983230072969 + 3 ^ 40 * 402733 * 2
def baseEnd_402733 : Nat := 206795604427278038985371

theorem tailTrace_402733 : CollatzResearch.WordTrace tailWord_402733 prefixEnd_402733 206795604427278038985371 := by
  unfold tailWord_402733
  simp only [CollatzResearch.WordTrace]
  refine ⟨14688879249974597165548853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9792586166649731443699235 14688879249974597165548853)
  ·
    refine ⟨1377082429685118484270205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14688879249974597165548853 1377082429685118484270205)
    ·
      refine ⟨516405911131919431601327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1377082429685118484270205 516405911131919431601327)
      ·
        refine ⟨774608866697879147401991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 516405911131919431601327 774608866697879147401991)
        ·
          refine ⟨1161913300046818721102987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 774608866697879147401991 1161913300046818721102987)
          ·
            refine ⟨1742869950070228081654481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1161913300046818721102987 1742869950070228081654481)
            ·
              refine ⟨1307152462552671061240861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1742869950070228081654481 1307152462552671061240861)
              ·
                refine ⟨490182173457251647965323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1307152462552671061240861 490182173457251647965323)
                ·
                  refine ⟨735273260185877471947985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 490182173457251647965323 735273260185877471947985)
                  ·
                    refine ⟨551454945139408103960989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 735273260185877471947985 551454945139408103960989)
                    ·
                      refine ⟨206795604427278038985371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 551454945139408103960989 206795604427278038985371)
                      ·
                        rfl

theorem cell23_402733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_402733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402733 prefixEnd_402733 := by exact prefixLift 402733
  have htrace : WordTrace (prefixWord ++ tailWord_402733) baseStart_402733 baseEnd_402733 := by
    simpa [prefixWord, tailWord_402733, baseEnd_402733] using wordTrace_append hprefix tailTrace_402733
  have hstable : (prefixWord ++ tailWord_402733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402733).length < 2 ^ (prefixWord ++ tailWord_402733).sum := by decide
  have hdescent : baseEnd_402733 < baseStart_402733 := by decide
  rcases family_descends (prefixWord ++ tailWord_402733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402746 : List Nat := [3, 1, 1, 1, 4, 1, 2, 4, 2, 1, 3]
def baseStart_402746 : Nat := 118140960795 + 402746 * 2 ^ 59
def prefixEnd_402746 : Nat := 4983230072969 + 3 ^ 40 * 402746 * 2
def baseEnd_402746 : Nat := 206802279675786488122811

theorem tailTrace_402746 : CollatzResearch.WordTrace tailWord_402746 prefixEnd_402746 206802279675786488122811 := by
  unfold tailWord_402746
  simp only [CollatzResearch.WordTrace]
  refine ⟨3672338349731875096443023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9792902265951666923848061 3672338349731875096443023)
  ·
    refine ⟨5508507524597812644664535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3672338349731875096443023 5508507524597812644664535)
    ·
      refine ⟨8262761286896718966996803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5508507524597812644664535 8262761286896718966996803)
      ·
        refine ⟨12394141930345078450495205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8262761286896718966996803 12394141930345078450495205)
        ·
          refine ⟨2323901611939702209467851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12394141930345078450495205 2323901611939702209467851)
          ·
            refine ⟨3485852417909553314201777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2323901611939702209467851 3485852417909553314201777)
            ·
              refine ⟨2614389313432164985651333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3485852417909553314201777 2614389313432164985651333)
              ·
                refine ⟨490197996268530934809625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2614389313432164985651333 490197996268530934809625)
                ·
                  refine ⟨367648497201398201107219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 490197996268530934809625 367648497201398201107219)
                  ·
                    refine ⟨551472745802097301660829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 367648497201398201107219 551472745802097301660829)
                    ·
                      refine ⟨206802279675786488122811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 551472745802097301660829 206802279675786488122811)
                      ·
                        rfl

theorem cell23_402746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4, 2, 1, 3].length) (baseStart_402746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402746 prefixEnd_402746 := by exact prefixLift 402746
  have htrace : WordTrace (prefixWord ++ tailWord_402746) baseStart_402746 baseEnd_402746 := by
    simpa [prefixWord, tailWord_402746, baseEnd_402746] using wordTrace_append hprefix tailTrace_402746
  have hstable : (prefixWord ++ tailWord_402746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402746).length < 2 ^ (prefixWord ++ tailWord_402746).sum := by decide
  have hdescent : baseEnd_402746 < baseStart_402746 := by decide
  rcases family_descends (prefixWord ++ tailWord_402746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402752 : List Nat := [2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 4]
def baseStart_402752 : Nat := 118140960795 + 402752 * 2 ^ 59
def prefixEnd_402752 : Nat := 4983230072969 + 3 ^ 40 * 402752 * 2
def baseEnd_402752 : Nat := 206805360559713464647783

theorem tailTrace_402752 : CollatzResearch.WordTrace tailWord_402752 prefixEnd_402752 206805360559713464647783 := by
  unfold tailWord_402752
  simp only [CollatzResearch.WordTrace]
  refine ⟨7344786118452881705245255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9793048157937175606993673 7344786118452881705245255)
  ·
    refine ⟨11017179177679322557867883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7344786118452881705245255 11017179177679322557867883)
    ·
      refine ⟨16525768766518983836801825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11017179177679322557867883 16525768766518983836801825)
      ·
        refine ⟨12394326574889237877601369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16525768766518983836801825 12394326574889237877601369)
        ·
          refine ⟨9295744931166928408201027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12394326574889237877601369 9295744931166928408201027)
          ·
            refine ⟨13943617396750392612301541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9295744931166928408201027 13943617396750392612301541)
            ·
              refine ⟨2614428261890698614806539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13943617396750392612301541 2614428261890698614806539)
              ·
                refine ⟨3921642392836047922209809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2614428261890698614806539 3921642392836047922209809)
                ·
                  refine ⟨2941231794627035941657357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3921642392836047922209809 2941231794627035941657357)
                  ·
                    refine ⟨1102961922985138478121509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2941231794627035941657357 1102961922985138478121509)
                    ·
                      refine ⟨206805360559713464647783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1102961922985138478121509 206805360559713464647783)
                      ·
                        rfl

theorem cell23_402752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 4].length) (baseStart_402752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402752 prefixEnd_402752 := by exact prefixLift 402752
  have htrace : WordTrace (prefixWord ++ tailWord_402752) baseStart_402752 baseEnd_402752 := by
    simpa [prefixWord, tailWord_402752, baseEnd_402752] using wordTrace_append hprefix tailTrace_402752
  have hstable : (prefixWord ++ tailWord_402752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402752).length < 2 ^ (prefixWord ++ tailWord_402752).sum := by decide
  have hdescent : baseEnd_402752 < baseStart_402752 := by decide
  rcases family_descends (prefixWord ++ tailWord_402752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402762 : List Nat := [3, 1, 2, 1, 1, 1, 1, 5, 2, 6]
def baseStart_402762 : Nat := 118140960795 + 402762 * 2 ^ 59
def prefixEnd_402762 : Nat := 4983230072969 + 3 ^ 40 * 402762 * 2
def baseEnd_402762 : Nat := 68936831788752808507579

theorem tailTrace_402762 : CollatzResearch.WordTrace tailWord_402762 prefixEnd_402762 68936831788752808507579 := by
  unfold tailWord_402762
  simp only [CollatzResearch.WordTrace]
  refine ⟨3672484241717383779588635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9793291311246356745569693 3672484241717383779588635)
  ·
    refine ⟨5508726362576075669382953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3672484241717383779588635 5508726362576075669382953)
    ·
      refine ⟨4131544771932056752037215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5508726362576075669382953 4131544771932056752037215)
      ·
        refine ⟨6197317157898085128055823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4131544771932056752037215 6197317157898085128055823)
        ·
          refine ⟨9295975736847127692083735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6197317157898085128055823 9295975736847127692083735)
          ·
            refine ⟨13943963605270691538125603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9295975736847127692083735 13943963605270691538125603)
            ·
              refine ⟨20915945407906037307188405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13943963605270691538125603 20915945407906037307188405)
              ·
                refine ⟨1960869881991190997548913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20915945407906037307188405 1960869881991190997548913)
                ·
                  refine ⟨1470652411493393248161685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1960869881991190997548913 1470652411493393248161685)
                  ·
                    refine ⟨68936831788752808507579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1470652411493393248161685 68936831788752808507579)
                    ·
                      rfl

theorem cell23_402762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_402762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402762 prefixEnd_402762 := by exact prefixLift 402762
  have htrace : WordTrace (prefixWord ++ tailWord_402762) baseStart_402762 baseEnd_402762 := by
    simpa [prefixWord, tailWord_402762, baseEnd_402762] using wordTrace_append hprefix tailTrace_402762
  have hstable : (prefixWord ++ tailWord_402762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402762).length < 2 ^ (prefixWord ++ tailWord_402762).sum := by decide
  have hdescent : baseEnd_402762 < baseStart_402762 := by decide
  rcases family_descends (prefixWord ++ tailWord_402762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402773 : List Nat := [1, 3, 2, 2, 3, 1, 3, 2, 1, 3, 2]
def baseStart_402773 : Nat := 118140960795 + 402773 * 2 ^ 59
def prefixEnd_402773 : Nat := 4983230072969 + 3 ^ 40 * 402773 * 2
def baseEnd_402773 : Nat := 206816143653457882485187

theorem tailTrace_402773 : CollatzResearch.WordTrace tailWord_402773 prefixEnd_402773 206816143653457882485187 := by
  unfold tailWord_402773
  simp only [CollatzResearch.WordTrace]
  refine ⟨14690338169829683997004973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9793558779886455998003315 14690338169829683997004973)
  ·
    refine ⟨5508876813686131498876865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14690338169829683997004973 5508876813686131498876865)
    ·
      refine ⟨4131657610264598624157649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5508876813686131498876865 4131657610264598624157649)
      ·
        refine ⟨3098743207698448968118237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4131657610264598624157649 3098743207698448968118237)
        ·
          refine ⟨1162028702886918363044339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3098743207698448968118237 1162028702886918363044339)
          ·
            refine ⟨1743043054330377544566509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1162028702886918363044339 1743043054330377544566509)
            ·
              refine ⟨653641145373891579212441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1743043054330377544566509 653641145373891579212441)
              ·
                refine ⟨490230859030418684409331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 653641145373891579212441 490230859030418684409331)
                ·
                  refine ⟨735346288545628026613997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 490230859030418684409331 735346288545628026613997)
                  ·
                    refine ⟨275754858204610509980249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 735346288545628026613997 275754858204610509980249)
                    ·
                      refine ⟨206816143653457882485187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 275754858204610509980249 206816143653457882485187)
                      ·
                        rfl

theorem cell23_402773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2, 1, 3, 2].length) (baseStart_402773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402773 prefixEnd_402773 := by exact prefixLift 402773
  have htrace : WordTrace (prefixWord ++ tailWord_402773) baseStart_402773 baseEnd_402773 := by
    simpa [prefixWord, tailWord_402773, baseEnd_402773] using wordTrace_append hprefix tailTrace_402773
  have hstable : (prefixWord ++ tailWord_402773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402773).length < 2 ^ (prefixWord ++ tailWord_402773).sum := by decide
  have hdescent : baseEnd_402773 < baseStart_402773 := by decide
  rcases family_descends (prefixWord ++ tailWord_402773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402819 : List Nat := [1, 1, 1, 3, 5, 1, 1, 1, 1, 5, 3]
def baseStart_402819 : Nat := 118140960795 + 402819 * 2 ^ 59
def prefixEnd_402819 : Nat := 4983230072969 + 3 ^ 40 * 402819 * 2
def baseEnd_402819 : Nat := 206839763763564702509975

theorem tailTrace_402819 : CollatzResearch.WordTrace tailWord_402819 prefixEnd_402819 206839763763564702509975 := by
  unfold tailWord_402819
  simp only [CollatzResearch.WordTrace]
  refine ⟨14692015927663033853179511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9794677285108689235453007 14692015927663033853179511)
  ·
    refine ⟨22038023891494550779769267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14692015927663033853179511 22038023891494550779769267)
    ·
      refine ⟨33057035837241826169653901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22038023891494550779769267 33057035837241826169653901)
      ·
        refine ⟨12396388438965684813620213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33057035837241826169653901 12396388438965684813620213)
        ·
          refine ⟨1162161416153032951276895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12396388438965684813620213 1162161416153032951276895)
          ·
            refine ⟨1743242124229549426915343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1162161416153032951276895 1743242124229549426915343)
            ·
              refine ⟨2614863186344324140373015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1743242124229549426915343 2614863186344324140373015)
              ·
                refine ⟨3922294779516486210559523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2614863186344324140373015 3922294779516486210559523)
                ·
                  refine ⟨5883442169274729315839285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3922294779516486210559523 5883442169274729315839285)
                  ·
                    refine ⟨551572703369505873359933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5883442169274729315839285 551572703369505873359933)
                    ·
                      refine ⟨206839763763564702509975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 551572703369505873359933 206839763763564702509975)
                      ·
                        rfl

theorem cell23_402819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 5, 3].length) (baseStart_402819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402819 prefixEnd_402819 := by exact prefixLift 402819
  have htrace : WordTrace (prefixWord ++ tailWord_402819) baseStart_402819 baseEnd_402819 := by
    simpa [prefixWord, tailWord_402819, baseEnd_402819] using wordTrace_append hprefix tailTrace_402819
  have hstable : (prefixWord ++ tailWord_402819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402819).length < 2 ^ (prefixWord ++ tailWord_402819).sum := by decide
  have hdescent : baseEnd_402819 < baseStart_402819 := by decide
  rcases family_descends (prefixWord ++ tailWord_402819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402920 : List Nat := [2, 1, 4, 1, 1, 2, 5, 2, 1, 4]
def baseStart_402920 : Nat := 118140960795 + 402920 * 2 ^ 59
def prefixEnd_402920 : Nat := 4983230072969 + 3 ^ 40 * 402920 * 2
def baseEnd_402920 : Nat := 68963875103222935782337

theorem tailTrace_402920 : CollatzResearch.WordTrace tailWord_402920 prefixEnd_402920 68963875103222935782337 := by
  unfold tailWord_402920
  simp only [CollatzResearch.WordTrace]
  refine ⟨7347849850148564051303107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9797133133531418735070809 7347849850148564051303107)
  ·
    refine ⟨11021774775222846076954661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7347849850148564051303107 11021774775222846076954661)
    ·
      refine ⟨2066582770354283639428999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11021774775222846076954661 2066582770354283639428999)
      ·
        refine ⟨3099874155531425459143499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2066582770354283639428999 3099874155531425459143499)
        ·
          refine ⟨4649811233297138188715249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3099874155531425459143499 4649811233297138188715249)
          ·
            refine ⟨3487358424972853641536437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4649811233297138188715249 3487358424972853641536437)
            ·
              refine ⟨326939852341205028894041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3487358424972853641536437 326939852341205028894041)
              ·
                refine ⟨245204889255903771670531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 326939852341205028894041 245204889255903771670531)
                ·
                  refine ⟨367807333883855657505797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 245204889255903771670531 367807333883855657505797)
                  ·
                    refine ⟨68963875103222935782337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 367807333883855657505797 68963875103222935782337)
                    ·
                      rfl

theorem cell23_402920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_402920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402920 prefixEnd_402920 := by exact prefixLift 402920
  have htrace : WordTrace (prefixWord ++ tailWord_402920) baseStart_402920 baseEnd_402920 := by
    simpa [prefixWord, tailWord_402920, baseEnd_402920] using wordTrace_append hprefix tailTrace_402920
  have hstable : (prefixWord ++ tailWord_402920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402920).length < 2 ^ (prefixWord ++ tailWord_402920).sum := by decide
  have hdescent : baseEnd_402920 < baseStart_402920 := by decide
  rcases family_descends (prefixWord ++ tailWord_402920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402933 : List Nat := [1, 3, 5, 1, 1, 2, 1, 3, 6]
def baseStart_402933 : Nat := 118140960795 + 402933 * 2 ^ 59
def prefixEnd_402933 : Nat := 4983230072969 + 3 ^ 40 * 402933 * 2
def baseEnd_402933 : Nat := 22988700062019695164939

theorem tailTrace_402933 : CollatzResearch.WordTrace tailWord_402933 prefixEnd_402933 22988700062019695164939 := by
  unfold tailWord_402933
  simp only [CollatzResearch.WordTrace]
  refine ⟨14696173849250031322829453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9797449232833354215219635 14696173849250031322829453)
  ·
    refine ⟨5511065193468761746061045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14696173849250031322829453 5511065193468761746061045)
    ·
      refine ⟨516662361887696413693223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5511065193468761746061045 516662361887696413693223)
      ·
        refine ⟨774993542831544620539835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 516662361887696413693223 774993542831544620539835)
        ·
          refine ⟨1162490314247316930809753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 774993542831544620539835 1162490314247316930809753)
          ·
            refine ⟨871867735685487698107315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1162490314247316930809753 871867735685487698107315)
            ·
              refine ⟨1307801603528231547160973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 871867735685487698107315 1307801603528231547160973)
              ·
                refine ⟨490425601323086830185365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1307801603528231547160973 490425601323086830185365)
                ·
                  refine ⟨22988700062019695164939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 490425601323086830185365 22988700062019695164939)
                  ·
                    rfl

theorem cell23_402933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 3, 6].length) (baseStart_402933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402933 prefixEnd_402933 := by exact prefixLift 402933
  have htrace : WordTrace (prefixWord ++ tailWord_402933) baseStart_402933 baseEnd_402933 := by
    simpa [prefixWord, tailWord_402933, baseEnd_402933] using wordTrace_append hprefix tailTrace_402933
  have hstable : (prefixWord ++ tailWord_402933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402933).length < 2 ^ (prefixWord ++ tailWord_402933).sum := by decide
  have hdescent : baseEnd_402933 < baseStart_402933 := by decide
  rcases family_descends (prefixWord ++ tailWord_402933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
