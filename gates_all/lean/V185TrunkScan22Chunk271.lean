import V185TrunkScan22Chunk270

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2416552 : List Nat := [2, 1, 6, 2, 2, 1, 1, 3, 1, 3]
def baseStart_2416552 : Nat := 118140960795 + 2416552 * 2 ^ 59
def prefixEnd_2416552 : Nat := 4983230072969 + 3 ^ 40 * 2416552 * 2
def baseEnd_2416552 : Nat := 827235135055956308590991

theorem tailTrace_2416552 : CollatzResearch.WordTrace tailWord_2416552 prefixEnd_2416552 827235135055956308590991 := by
  unfold tailWord_2416552
  simp only [CollatzResearch.WordTrace]
  refine ⟨44069446170626146534425955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58759261560834862045901273 44069446170626146534425955)
  ·
    refine ⟨66104169255939219801638933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44069446170626146534425955 66104169255939219801638933)
    ·
      refine ⟨3098632933872150928201825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 66104169255939219801638933 3098632933872150928201825)
      ·
        refine ⟨2323974700404113196151369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3098632933872150928201825 2323974700404113196151369)
        ·
          refine ⟨1742981025303084897113527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2323974700404113196151369 1742981025303084897113527)
          ·
            refine ⟨2614471537954627345670291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1742981025303084897113527 2614471537954627345670291)
            ·
              refine ⟨3921707306931941018505437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2614471537954627345670291 3921707306931941018505437)
              ·
                refine ⟨1470640240099477881939539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3921707306931941018505437 1470640240099477881939539)
                ·
                  refine ⟨2205960360149216822909309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1470640240099477881939539 2205960360149216822909309)
                  ·
                    refine ⟨827235135055956308590991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2205960360149216822909309 827235135055956308590991)
                    ·
                      rfl

theorem cell22_2416552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_2416552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2416552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2416552 prefixEnd_2416552 := by exact prefixLift 2416552
  have htrace : WordTrace (prefixWord ++ tailWord_2416552) baseStart_2416552 baseEnd_2416552 := by
    simpa [prefixWord, tailWord_2416552, baseEnd_2416552] using wordTrace_append hprefix tailTrace_2416552
  have hstable : (prefixWord ++ tailWord_2416552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416552).length < 2 ^ (prefixWord ++ tailWord_2416552).sum := by decide
  have hdescent : baseEnd_2416552 < baseStart_2416552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416574 : List Nat := [4, 2, 1, 1, 1, 3, 2, 1, 4, 3]
def baseStart_2416574 : Nat := 118140960795 + 2416574 * 2 ^ 59
def prefixEnd_2416574 : Nat := 4983230072969 + 3 ^ 40 * 2416574 * 2
def baseEnd_2416574 : Nat := 827242666105555584540923

theorem tailTrace_2416574 : CollatzResearch.WordTrace tailWord_2416574 prefixEnd_2416574 827242666105555584540923 := by
  unfold tailWord_2416574
  simp only [CollatzResearch.WordTrace]
  refine ⟨11017461843396573853269097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58759796498115060550768517 11017461843396573853269097)
  ·
    refine ⟨8263096382547430389951823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11017461843396573853269097 8263096382547430389951823)
    ·
      refine ⟨12394644573821145584927735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8263096382547430389951823 12394644573821145584927735)
      ·
        refine ⟨18591966860731718377391603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12394644573821145584927735 18591966860731718377391603)
        ·
          refine ⟨27887950291097577566087405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18591966860731718377391603 27887950291097577566087405)
          ·
            refine ⟨10457981359161591587282777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27887950291097577566087405 10457981359161591587282777)
            ·
              refine ⟨7843486019371193690462083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10457981359161591587282777 7843486019371193690462083)
              ·
                refine ⟨11765229029056790535693125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7843486019371193690462083 11765229029056790535693125)
                ·
                  refine ⟨2205980442948148225442461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11765229029056790535693125 2205980442948148225442461)
                  ·
                    refine ⟨827242666105555584540923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2205980442948148225442461 827242666105555584540923)
                    ·
                      rfl

theorem cell22_2416574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_2416574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2416574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2416574 prefixEnd_2416574 := by exact prefixLift 2416574
  have htrace : WordTrace (prefixWord ++ tailWord_2416574) baseStart_2416574 baseEnd_2416574 := by
    simpa [prefixWord, tailWord_2416574, baseEnd_2416574] using wordTrace_append hprefix tailTrace_2416574
  have hstable : (prefixWord ++ tailWord_2416574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416574).length < 2 ^ (prefixWord ++ tailWord_2416574).sum := by decide
  have hdescent : baseEnd_2416574 < baseStart_2416574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416632 : List Nat := [2, 1, 2, 1, 1, 3, 3, 4, 5]
def baseStart_2416632 : Nat := 118140960795 + 2416632 * 2 ^ 59
def prefixEnd_2416632 : Nat := 4983230072969 + 3 ^ 40 * 2416632 * 2
def baseEnd_2416632 : Nat := 275754173563620922196915

theorem tailTrace_2416632 : CollatzResearch.WordTrace tailWord_2416632 prefixEnd_2416632 275754173563620922196915 := by
  unfold tailWord_2416632
  simp only [CollatzResearch.WordTrace]
  refine ⟨44070905090481233365882075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58761206787308311154509433 44070905090481233365882075)
  ·
    refine ⟨66106357635721850048823113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44070905090481233365882075 66106357635721850048823113)
    ·
      refine ⟨49579768226791387536617335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66106357635721850048823113 49579768226791387536617335)
      ·
        refine ⟨74369652340187081304926003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49579768226791387536617335 74369652340187081304926003)
        ·
          refine ⟨111554478510280621957389005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74369652340187081304926003 111554478510280621957389005)
          ·
            refine ⟨41832929441355233234020877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111554478510280621957389005 41832929441355233234020877)
            ·
              refine ⟨15687348540508212462757829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41832929441355233234020877 15687348540508212462757829)
              ·
                refine ⟨2941377851345289836767093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15687348540508212462757829 2941377851345289836767093)
                ·
                  refine ⟨275754173563620922196915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2941377851345289836767093 275754173563620922196915)
                  ·
                    rfl

theorem cell22_2416632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4, 5].length) (baseStart_2416632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2416632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2416632 prefixEnd_2416632 := by exact prefixLift 2416632
  have htrace : WordTrace (prefixWord ++ tailWord_2416632) baseStart_2416632 baseEnd_2416632 := by
    simpa [prefixWord, tailWord_2416632, baseEnd_2416632] using wordTrace_append hprefix tailTrace_2416632
  have hstable : (prefixWord ++ tailWord_2416632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416632).length < 2 ^ (prefixWord ++ tailWord_2416632).sum := by decide
  have hdescent : baseEnd_2416632 < baseStart_2416632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416636 : List Nat := [2, 2, 2, 1, 2, 2, 3, 4, 1, 3]
def baseStart_2416636 : Nat := 118140960795 + 2416636 * 2 ^ 59
def prefixEnd_2416636 : Nat := 4983230072969 + 3 ^ 40 * 2416636 * 2
def baseEnd_2416636 : Nat := 827263889972608089490733

theorem tailTrace_2416636 : CollatzResearch.WordTrace tailWord_2416636 prefixEnd_2416636 827263889972608089490733 := by
  unfold tailWord_2416636
  simp only [CollatzResearch.WordTrace]
  refine ⟨44070978036473987707454881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58761304048631983609939841 44070978036473987707454881)
  ·
    refine ⟨33053233527355490780591161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44070978036473987707454881 33053233527355490780591161)
    ·
      refine ⟨24789925145516618085443371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33053233527355490780591161 24789925145516618085443371)
      ·
        refine ⟨37184887718274927128165057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24789925145516618085443371 37184887718274927128165057)
        ·
          refine ⟨27888665788706195346123793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37184887718274927128165057 27888665788706195346123793)
          ·
            refine ⟨20916499341529646509592845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27888665788706195346123793 20916499341529646509592845)
            ·
              refine ⟨7843687253073617441097317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20916499341529646509592845 7843687253073617441097317)
              ·
                refine ⟨1470691359951303270205747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7843687253073617441097317 1470691359951303270205747)
                ·
                  refine ⟨2206037039926954905308621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1470691359951303270205747 2206037039926954905308621)
                  ·
                    refine ⟨827263889972608089490733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2206037039926954905308621 827263889972608089490733)
                    ·
                      rfl

theorem cell22_2416636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 4, 1, 3].length) (baseStart_2416636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2416636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2416636 prefixEnd_2416636 := by exact prefixLift 2416636
  have htrace : WordTrace (prefixWord ++ tailWord_2416636) baseStart_2416636 baseEnd_2416636 := by
    simpa [prefixWord, tailWord_2416636, baseEnd_2416636] using wordTrace_append hprefix tailTrace_2416636
  have hstable : (prefixWord ++ tailWord_2416636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416636).length < 2 ^ (prefixWord ++ tailWord_2416636).sum := by decide
  have hdescent : baseEnd_2416636 < baseStart_2416636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416647 : List Nat := [1, 1, 4, 3, 1, 2, 1, 1, 1, 7]
def baseStart_2416647 : Nat := 118140960795 + 2416647 * 2 ^ 59
def prefixEnd_2416647 : Nat := 4983230072969 + 3 ^ 40 * 2416647 * 2
def baseEnd_2416647 : Nat := 827267655497407727465699

theorem tailTrace_2416647 : CollatzResearch.WordTrace tailWord_2416647 prefixEnd_2416647 827267655497407727465699 := by
  unfold tailWord_2416647
  simp only [CollatzResearch.WordTrace]
  refine ⟨88142357275908124293560195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58761571517272082862373463 88142357275908124293560195)
  ·
    refine ⟨132213535913862186440340293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88142357275908124293560195 132213535913862186440340293)
    ·
      refine ⟨24790037983849159957563805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132213535913862186440340293 24790037983849159957563805)
      ·
        refine ⟨9296264243943434984086427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24790037983849159957563805 9296264243943434984086427)
        ·
          refine ⟨13944396365915152476129641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9296264243943434984086427 13944396365915152476129641)
          ·
            refine ⟨10458297274436364357097231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13944396365915152476129641 10458297274436364357097231)
            ·
              refine ⟨15687445911654546535645847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10458297274436364357097231 15687445911654546535645847)
              ·
                refine ⟨23531168867481819803468771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15687445911654546535645847 23531168867481819803468771)
                ·
                  refine ⟨35296753301222729705203157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23531168867481819803468771 35296753301222729705203157)
                  ·
                    refine ⟨827267655497407727465699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35296753301222729705203157 827267655497407727465699)
                    ·
                      rfl

theorem cell22_2416647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_2416647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2416647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2416647 prefixEnd_2416647 := by exact prefixLift 2416647
  have htrace : WordTrace (prefixWord ++ tailWord_2416647) baseStart_2416647 baseEnd_2416647 := by
    simpa [prefixWord, tailWord_2416647, baseEnd_2416647] using wordTrace_append hprefix tailTrace_2416647
  have hstable : (prefixWord ++ tailWord_2416647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416647).length < 2 ^ (prefixWord ++ tailWord_2416647).sum := by decide
  have hdescent : baseEnd_2416647 < baseStart_2416647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416707 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 6, 4]
def baseStart_2416707 : Nat := 118140960795 + 2416707 * 2 ^ 59
def prefixEnd_2416707 : Nat := 4983230072969 + 3 ^ 40 * 2416707 * 2
def baseEnd_2416707 : Nat := 827288194723587570965515

theorem tailTrace_2416707 : CollatzResearch.WordTrace tailWord_2416707 prefixEnd_2416707 827288194723587570965515 := by
  unfold tailWord_2416707
  simp only [CollatzResearch.WordTrace]
  refine ⟨88144545655690754540744375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58763030437127169693829583 88144545655690754540744375)
  ·
    refine ⟨132216818483536131811116563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88144545655690754540744375 132216818483536131811116563)
    ·
      refine ⟨198325227725304197716674845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132216818483536131811116563 198325227725304197716674845)
      ·
        refine ⟨74371960396989074143753067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198325227725304197716674845 74371960396989074143753067)
        ·
          refine ⟨111557940595483611215629601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74371960396989074143753067 111557940595483611215629601)
          ·
            refine ⟨83668455446612708411722201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111557940595483611215629601 83668455446612708411722201)
            ·
              refine ⟨62751341584959531308791651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83668455446612708411722201 62751341584959531308791651)
              ·
                refine ⟨94127012377439296963187477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62751341584959531308791651 94127012377439296963187477)
                ·
                  refine ⟨4412203705192467045149413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 94127012377439296963187477 4412203705192467045149413)
                  ·
                    refine ⟨827288194723587570965515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4412203705192467045149413 827288194723587570965515)
                    ·
                      rfl

theorem cell22_2416707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6, 4].length) (baseStart_2416707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2416707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2416707 prefixEnd_2416707 := by exact prefixLift 2416707
  have htrace : WordTrace (prefixWord ++ tailWord_2416707) baseStart_2416707 baseEnd_2416707 := by
    simpa [prefixWord, tailWord_2416707, baseEnd_2416707] using wordTrace_append hprefix tailTrace_2416707
  have hstable : (prefixWord ++ tailWord_2416707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416707).length < 2 ^ (prefixWord ++ tailWord_2416707).sum := by decide
  have hdescent : baseEnd_2416707 < baseStart_2416707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416724 : List Nat := [2, 4, 1, 1, 1, 1, 1, 5, 2, 4]
def baseStart_2416724 : Nat := 118140960795 + 2416724 * 2 ^ 59
def prefixEnd_2416724 : Nat := 4983230072969 + 3 ^ 40 * 2416724 * 2
def baseEnd_2416724 : Nat := 827294014171005193290463

theorem tailTrace_2416724 : CollatzResearch.WordTrace tailWord_2416724 prefixEnd_2416724 827294014171005193290463 := by
  unfold tailWord_2416724
  simp only [CollatzResearch.WordTrace]
  refine ⟨44072582848314583222056613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58763443797752777629408817 44072582848314583222056613)
  ·
    refine ⟨8263609284058984354135615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44072582848314583222056613 8263609284058984354135615)
    ·
      refine ⟨12395413926088476531203423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8263609284058984354135615 12395413926088476531203423)
      ·
        refine ⟨18593120889132714796805135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12395413926088476531203423 18593120889132714796805135)
        ·
          refine ⟨27889681333699072195207703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18593120889132714796805135 27889681333699072195207703)
          ·
            refine ⟨41834522000548608292811555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27889681333699072195207703 41834522000548608292811555)
            ·
              refine ⟨62751783000822912439217333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41834522000548608292811555 62751783000822912439217333)
              ·
                refine ⟨5882979656327148041176625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62751783000822912439217333 5882979656327148041176625)
                ·
                  refine ⟨4412234742245361030882469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5882979656327148041176625 4412234742245361030882469)
                  ·
                    refine ⟨827294014171005193290463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4412234742245361030882469 827294014171005193290463)
                    ·
                      rfl

theorem cell22_2416724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_2416724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2416724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2416724 prefixEnd_2416724 := by exact prefixLift 2416724
  have htrace : WordTrace (prefixWord ++ tailWord_2416724) baseStart_2416724 baseEnd_2416724 := by
    simpa [prefixWord, tailWord_2416724, baseEnd_2416724] using wordTrace_append hprefix tailTrace_2416724
  have hstable : (prefixWord ++ tailWord_2416724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416724).length < 2 ^ (prefixWord ++ tailWord_2416724).sum := by decide
  have hdescent : baseEnd_2416724 < baseStart_2416724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416790 : List Nat := [5, 3, 2, 1, 1, 10]
def baseStart_2416790 : Nat := 118140960795 + 2416790 * 2 ^ 59
def prefixEnd_2416790 : Nat := 4983230072969 + 3 ^ 40 * 2416790 * 2
def baseEnd_2416790 : Nat := 10213785275553123717781

theorem tailTrace_2416790 : CollatzResearch.WordTrace tailWord_2416790 prefixEnd_2416790 10213785275553123717781 := by
  unfold tailWord_2416790
  simp only [CollatzResearch.WordTrace]
  refine ⟨5509223307149378732250989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58765048609593373144010549 5509223307149378732250989)
  ·
    refine ⟨2065958740181017024594121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5509223307149378732250989 2065958740181017024594121)
    ·
      refine ⟨1549469055135762768445591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2065958740181017024594121 1549469055135762768445591)
      ·
        refine ⟨2324203582703644152668387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1549469055135762768445591 2324203582703644152668387)
        ·
          refine ⟨3486305374055466229002581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2324203582703644152668387 3486305374055466229002581)
          ·
            refine ⟨10213785275553123717781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3486305374055466229002581 10213785275553123717781)
            ·
              rfl

theorem cell22_2416790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 10].length) (baseStart_2416790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2416790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2416790 prefixEnd_2416790 := by exact prefixLift 2416790
  have htrace : WordTrace (prefixWord ++ tailWord_2416790) baseStart_2416790 baseEnd_2416790 := by
    simpa [prefixWord, tailWord_2416790, baseEnd_2416790] using wordTrace_append hprefix tailTrace_2416790
  have hstable : (prefixWord ++ tailWord_2416790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416790).length < 2 ^ (prefixWord ++ tailWord_2416790).sum := by decide
  have hdescent : baseEnd_2416790 < baseStart_2416790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416801 : List Nat := [1, 2, 3, 3, 1, 3, 2, 2, 5]
def baseStart_2416801 : Nat := 118140960795 + 2416801 * 2 ^ 59
def prefixEnd_2416801 : Nat := 4983230072969 + 3 ^ 40 * 2416801 * 2
def baseEnd_2416801 : Nat := 275773457614867553038409

theorem tailTrace_2416801 : CollatzResearch.WordTrace tailWord_2416801 prefixEnd_2416801 275773457614867553038409 := by
  unfold tailWord_2416801
  simp only [CollatzResearch.WordTrace]
  refine ⟨88147974117350208594666257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58765316078233472396444171 88147974117350208594666257)
  ·
    refine ⟨66110980588012656445999693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88147974117350208594666257 66110980588012656445999693)
    ·
      refine ⟨24791617720504746167249885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66110980588012656445999693 24791617720504746167249885)
      ·
        refine ⟨9296856645189279812718707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24791617720504746167249885 9296856645189279812718707)
        ·
          refine ⟨13945284967783919719078061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9296856645189279812718707 13945284967783919719078061)
          ·
            refine ⟨5229481862918969894654273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13945284967783919719078061 5229481862918969894654273)
            ·
              refine ⟨3922111397189227420990705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5229481862918969894654273 3922111397189227420990705)
              ·
                refine ⟨2941583547891920565743029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3922111397189227420990705 2941583547891920565743029)
                ·
                  refine ⟨275773457614867553038409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2941583547891920565743029 275773457614867553038409)
                  ·
                    rfl

theorem cell22_2416801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2, 5].length) (baseStart_2416801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2416801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2416801 prefixEnd_2416801 := by exact prefixLift 2416801
  have htrace : WordTrace (prefixWord ++ tailWord_2416801) baseStart_2416801 baseEnd_2416801 := by
    simpa [prefixWord, tailWord_2416801, baseEnd_2416801] using wordTrace_append hprefix tailTrace_2416801
  have hstable : (prefixWord ++ tailWord_2416801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416801).length < 2 ^ (prefixWord ++ tailWord_2416801).sum := by decide
  have hdescent : baseEnd_2416801 < baseStart_2416801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416874 : List Nat := [3, 1, 3, 1, 1, 2, 2, 9]
def baseStart_2416874 : Nat := 118140960795 + 2416874 * 2 ^ 59
def prefixEnd_2416874 : Nat := 4983230072969 + 3 ^ 40 * 2416874 * 2
def baseEnd_2416874 : Nat := 91927262470717200226667

theorem tailTrace_2416874 : CollatzResearch.WordTrace tailWord_2416874 prefixEnd_2416874 91927262470717200226667 := by
  unfold tailWord_2416874
  simp only [CollatzResearch.WordTrace]
  refine ⟨22037659161521435515518419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58767091097390494708049117 22037659161521435515518419)
  ·
    refine ⟨33056488742282153273277629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22037659161521435515518419 33056488742282153273277629)
    ·
      refine ⟨12396183278355807477479111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33056488742282153273277629 12396183278355807477479111)
      ·
        refine ⟨18594274917533711216218667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12396183278355807477479111 18594274917533711216218667)
        ·
          refine ⟨27891412376300566824328001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18594274917533711216218667 27891412376300566824328001)
          ·
            refine ⟨20918559282225425118246001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27891412376300566824328001 20918559282225425118246001)
            ·
              refine ⟨15688919461669068838684501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20918559282225425118246001 15688919461669068838684501)
              ·
                refine ⟨91927262470717200226667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15688919461669068838684501 91927262470717200226667)
                ·
                  rfl

theorem cell22_2416874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 9].length) (baseStart_2416874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2416874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2416874 prefixEnd_2416874 := by exact prefixLift 2416874
  have htrace : WordTrace (prefixWord ++ tailWord_2416874) baseStart_2416874 baseEnd_2416874 := by
    simpa [prefixWord, tailWord_2416874, baseEnd_2416874] using wordTrace_append hprefix tailTrace_2416874
  have hstable : (prefixWord ++ tailWord_2416874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416874).length < 2 ^ (prefixWord ++ tailWord_2416874).sum := by decide
  have hdescent : baseEnd_2416874 < baseStart_2416874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416906 : List Nat := [3, 1, 2, 2, 1, 1, 2, 2, 5, 3]
def baseStart_2416906 : Nat := 118140960795 + 2416906 * 2 ^ 59
def prefixEnd_2416906 : Nat := 4983230072969 + 3 ^ 40 * 2416906 * 2
def baseEnd_2416906 : Nat := 827356316490417385239905

theorem tailTrace_2416906 : CollatzResearch.WordTrace tailWord_2416906 prefixEnd_2416906 827356316490417385239905 := by
  unfold tailWord_2416906
  simp only [CollatzResearch.WordTrace]
  refine ⟨22037950945492452881809643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58767869187979874351492381 22037950945492452881809643)
  ·
    refine ⟨33056926418238679322714465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22037950945492452881809643 33056926418238679322714465)
    ·
      refine ⟨24792694813679009492035849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33056926418238679322714465 24792694813679009492035849)
      ·
        refine ⟨18594521110259257119026887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24792694813679009492035849 18594521110259257119026887)
        ·
          refine ⟨27891781665388885678540331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18594521110259257119026887 27891781665388885678540331)
          ·
            refine ⟨41837672498083328517810497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27891781665388885678540331 41837672498083328517810497)
            ·
              refine ⟨31378254373562496388357873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41837672498083328517810497 31378254373562496388357873)
              ·
                refine ⟨23533690780171872291268405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31378254373562496388357873 23533690780171872291268405)
                ·
                  refine ⟨2206283510641113027306413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23533690780171872291268405 2206283510641113027306413)
                  ·
                    refine ⟨827356316490417385239905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2206283510641113027306413 827356316490417385239905)
                    ·
                      rfl

theorem cell22_2416906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 5, 3].length) (baseStart_2416906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2416906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2416906 prefixEnd_2416906 := by exact prefixLift 2416906
  have htrace : WordTrace (prefixWord ++ tailWord_2416906) baseStart_2416906 baseEnd_2416906 := by
    simpa [prefixWord, tailWord_2416906, baseEnd_2416906] using wordTrace_append hprefix tailTrace_2416906
  have hstable : (prefixWord ++ tailWord_2416906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416906).length < 2 ^ (prefixWord ++ tailWord_2416906).sum := by decide
  have hdescent : baseEnd_2416906 < baseStart_2416906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416923 : List Nat := [1, 1, 1, 1, 1, 1, 6, 6, 1, 3]
def baseStart_2416923 : Nat := 118140960795 + 2416923 * 2 ^ 59
def prefixEnd_2416923 : Nat := 4983230072969 + 3 ^ 40 * 2416923 * 2
def baseEnd_2416923 : Nat := 827362135937835007564853

theorem tailTrace_2416923 : CollatzResearch.WordTrace tailWord_2416923 prefixEnd_2416923 827362135937835007564853 := by
  unfold tailWord_2416923
  simp only [CollatzResearch.WordTrace]
  refine ⟨88152423822908223430607423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58768282548605482287071615 88152423822908223430607423)
  ·
    refine ⟨132228635734362335145911135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88152423822908223430607423 132228635734362335145911135)
    ·
      refine ⟨198342953601543502718866703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132228635734362335145911135 198342953601543502718866703)
      ·
        refine ⟨297514430402315254078300055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198342953601543502718866703 297514430402315254078300055)
        ·
          refine ⟨446271645603472881117450083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297514430402315254078300055 446271645603472881117450083)
          ·
            refine ⟨669407468405209321676175125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 446271645603472881117450083 669407468405209321676175125)
            ·
              refine ⟨31378475081494186953570709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 669407468405209321676175125 31378475081494186953570709)
              ·
                refine ⟨1470866019445040013448627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31378475081494186953570709 1470866019445040013448627)
                ·
                  refine ⟨2206299029167560020172941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1470866019445040013448627 2206299029167560020172941)
                  ·
                    refine ⟨827362135937835007564853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2206299029167560020172941 827362135937835007564853)
                    ·
                      rfl

theorem cell22_2416923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6, 1, 3].length) (baseStart_2416923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2416923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2416923 prefixEnd_2416923 := by exact prefixLift 2416923
  have htrace : WordTrace (prefixWord ++ tailWord_2416923) baseStart_2416923 baseEnd_2416923 := by
    simpa [prefixWord, tailWord_2416923, baseEnd_2416923] using wordTrace_append hprefix tailTrace_2416923
  have hstable : (prefixWord ++ tailWord_2416923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416923).length < 2 ^ (prefixWord ++ tailWord_2416923).sum := by decide
  have hdescent : baseEnd_2416923 < baseStart_2416923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417013 : List Nat := [1, 3, 4, 1, 2, 1, 2, 2, 1, 5]
def baseStart_2417013 : Nat := 118140960795 + 2417013 * 2 ^ 59
def prefixEnd_2417013 : Nat := 4983230072969 + 3 ^ 40 * 2417013 * 2
def baseEnd_2417013 : Nat := 827392944777104772814577

theorem tailTrace_2417013 : CollatzResearch.WordTrace tailWord_2417013 prefixEnd_2417013 827392944777104772814577 := by
  unfold tailWord_2417013
  simp only [CollatzResearch.WordTrace]
  refine ⟨88155706392582168801383693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58770470928388112534255795 88155706392582168801383693)
  ·
    refine ⟨33058389897218313300518885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88155706392582168801383693 33058389897218313300518885)
    ·
      refine ⟨6198448105728433743847291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33058389897218313300518885 6198448105728433743847291)
      ·
        refine ⟨9297672158592650615770937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6198448105728433743847291 9297672158592650615770937)
        ·
          refine ⟨6973254118944487961828203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9297672158592650615770937 6973254118944487961828203)
          ·
            refine ⟨10459881178416731942742305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6973254118944487961828203 10459881178416731942742305)
            ·
              refine ⟨7844910883812548957056729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10459881178416731942742305 7844910883812548957056729)
              ·
                refine ⟨5883683162859411717792547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7844910883812548957056729 5883683162859411717792547)
                ·
                  refine ⟨8825524744289117576688821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5883683162859411717792547 8825524744289117576688821)
                  ·
                    refine ⟨827392944777104772814577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8825524744289117576688821 827392944777104772814577)
                    ·
                      rfl

theorem cell22_2417013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_2417013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2417013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2417013 prefixEnd_2417013 := by exact prefixLift 2417013
  have htrace : WordTrace (prefixWord ++ tailWord_2417013) baseStart_2417013 baseEnd_2417013 := by
    simpa [prefixWord, tailWord_2417013, baseEnd_2417013] using wordTrace_append hprefix tailTrace_2417013
  have hstable : (prefixWord ++ tailWord_2417013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417013).length < 2 ^ (prefixWord ++ tailWord_2417013).sum := by decide
  have hdescent : baseEnd_2417013 < baseStart_2417013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417066 : List Nat := [3, 1, 6, 1, 1, 2, 1, 3, 4]
def baseStart_2417066 : Nat := 118140960795 + 2417066 * 2 ^ 59
def prefixEnd_2417066 : Nat := 4983230072969 + 3 ^ 40 * 2417066 * 2
def baseEnd_2417066 : Nat := 275803695920076767079805

theorem tailTrace_2417066 : CollatzResearch.WordTrace tailWord_2417066 prefixEnd_2417066 275803695920076767079805 := by
  unfold tailWord_2417066
  simp only [CollatzResearch.WordTrace]
  refine ⟨22039409865347539713265763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58771759640926772568708701 22039409865347539713265763)
  ·
    refine ⟨33059114798021309569898645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22039409865347539713265763 33059114798021309569898645)
    ·
      refine ⟨1549646006157248886088999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 33059114798021309569898645 1549646006157248886088999)
      ·
        refine ⟨2324469009235873329133499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1549646006157248886088999 2324469009235873329133499)
        ·
          refine ⟨3486703513853809993700249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2324469009235873329133499 3486703513853809993700249)
          ·
            refine ⟨2615027635390357495275187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3486703513853809993700249 2615027635390357495275187)
            ·
              refine ⟨3922541453085536242912781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2615027635390357495275187 3922541453085536242912781)
              ·
                refine ⟨1470953044907076091092293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3922541453085536242912781 1470953044907076091092293)
                ·
                  refine ⟨275803695920076767079805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1470953044907076091092293 275803695920076767079805)
                  ·
                    rfl

theorem cell22_2417066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 3, 4].length) (baseStart_2417066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2417066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2417066 prefixEnd_2417066 := by exact prefixLift 2417066
  have htrace : WordTrace (prefixWord ++ tailWord_2417066) baseStart_2417066 baseEnd_2417066 := by
    simpa [prefixWord, tailWord_2417066, baseEnd_2417066] using wordTrace_append hprefix tailTrace_2417066
  have hstable : (prefixWord ++ tailWord_2417066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417066).length < 2 ^ (prefixWord ++ tailWord_2417066).sum := by decide
  have hdescent : baseEnd_2417066 < baseStart_2417066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417161 : List Nat := [1, 2, 1, 1, 3, 1, 2, 11]
def baseStart_2417161 : Nat := 118140960795 + 2417161 * 2 ^ 59
def prefixEnd_2417161 : Nat := 4983230072969 + 3 ^ 40 * 2417161 * 2
def baseEnd_2417161 : Nat := 91938178689075746679347

theorem tailTrace_2417161 : CollatzResearch.WordTrace tailWord_2417161 prefixEnd_2417161 91938178689075746679347 := by
  unfold tailWord_2417161
  simp only [CollatzResearch.WordTrace]
  refine ⟨88161104396045990077771337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58774069597363993385180891 88161104396045990077771337)
  ·
    refine ⟨66120828297034492558328503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88161104396045990077771337 66120828297034492558328503)
    ·
      refine ⟨99181242445551738837492755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66120828297034492558328503 99181242445551738837492755)
      ·
        refine ⟨148771863668327608256239133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99181242445551738837492755 148771863668327608256239133)
        ·
          refine ⟨55789448875622853096089675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148771863668327608256239133 55789448875622853096089675)
          ·
            refine ⟨83684173313434279644134513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55789448875622853096089675 83684173313434279644134513)
            ·
              refine ⟨62763129985075709733100885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83684173313434279644134513 62763129985075709733100885)
              ·
                refine ⟨91938178689075746679347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 62763129985075709733100885 91938178689075746679347)
                ·
                  rfl

theorem cell22_2417161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 11].length) (baseStart_2417161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2417161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2417161 prefixEnd_2417161 := by exact prefixLift 2417161
  have htrace : WordTrace (prefixWord ++ tailWord_2417161) baseStart_2417161 baseEnd_2417161 := by
    simpa [prefixWord, tailWord_2417161, baseEnd_2417161] using wordTrace_append hprefix tailTrace_2417161
  have hstable : (prefixWord ++ tailWord_2417161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417161).length < 2 ^ (prefixWord ++ tailWord_2417161).sum := by decide
  have hdescent : baseEnd_2417161 < baseStart_2417161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417180 : List Nat := [2, 2, 3, 1, 2, 2, 3, 1, 2, 4]
def baseStart_2417180 : Nat := 118140960795 + 2417180 * 2 ^ 59
def prefixEnd_2417180 : Nat := 4983230072969 + 3 ^ 40 * 2417180 * 2
def baseEnd_2417180 : Nat := 827450112289972003889065

theorem tailTrace_2417180 : CollatzResearch.WordTrace tailWord_2417180 prefixEnd_2417180 827450112289972003889065 := by
  unfold tailWord_2417180
  simp only [CollatzResearch.WordTrace]
  refine ⟨44080898691488578161356497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58774531588651437548475329 44080898691488578161356497)
  ·
    refine ⟨33060674018616433621017373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44080898691488578161356497 33060674018616433621017373)
    ·
      refine ⟨12397752756981162607881515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33060674018616433621017373 12397752756981162607881515)
      ·
        refine ⟨18596629135471743911822273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12397752756981162607881515 18596629135471743911822273)
        ·
          refine ⟨13947471851603807933866705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18596629135471743911822273 13947471851603807933866705)
          ·
            refine ⟨10460603888702855950400029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13947471851603807933866705 10460603888702855950400029)
            ·
              refine ⟨3922726458263570981400011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10460603888702855950400029 3922726458263570981400011)
              ·
                refine ⟨5884089687395356472100017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3922726458263570981400011 5884089687395356472100017)
                ·
                  refine ⟨4413067265546517354075013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5884089687395356472100017 4413067265546517354075013)
                  ·
                    refine ⟨827450112289972003889065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4413067265546517354075013 827450112289972003889065)
                    ·
                      rfl

theorem cell22_2417180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_2417180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2417180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2417180 prefixEnd_2417180 := by exact prefixLift 2417180
  have htrace : WordTrace (prefixWord ++ tailWord_2417180) baseStart_2417180 baseEnd_2417180 := by
    simpa [prefixWord, tailWord_2417180, baseEnd_2417180] using wordTrace_append hprefix tailTrace_2417180
  have hstable : (prefixWord ++ tailWord_2417180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417180).length < 2 ^ (prefixWord ++ tailWord_2417180).sum := by decide
  have hdescent : baseEnd_2417180 < baseStart_2417180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417210 : List Nat := [3, 1, 1, 1, 3, 3, 1, 3, 3, 3]
def baseStart_2417210 : Nat := 118140960795 + 2417210 * 2 ^ 59
def prefixEnd_2417210 : Nat := 4983230072969 + 3 ^ 40 * 2417210 * 2
def baseEnd_2417210 : Nat := 827460381903061925638973

theorem tailTrace_2417210 : CollatzResearch.WordTrace tailWord_2417210 prefixEnd_2417210 827460381903061925638973 := by
  unfold tailWord_2417210
  simp only [CollatzResearch.WordTrace]
  refine ⟨22040722893217117861576271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58775261048578980964203389 22040722893217117861576271)
  ·
    refine ⟨33061084339825676792364407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22040722893217117861576271 33061084339825676792364407)
    ·
      refine ⟨49591626509738515188546611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33061084339825676792364407 49591626509738515188546611)
      ·
        refine ⟨74387439764607772782819917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49591626509738515188546611 74387439764607772782819917)
        ·
          refine ⟨27895289911727914793557469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74387439764607772782819917 27895289911727914793557469)
          ·
            refine ⟨10460733716897968047584051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27895289911727914793557469 10460733716897968047584051)
            ·
              refine ⟨15691100575346952071376077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10460733716897968047584051 15691100575346952071376077)
              ·
                refine ⟨5884162715755107026766029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15691100575346952071376077 5884162715755107026766029)
                ·
                  refine ⟨2206561018408165135037261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5884162715755107026766029 2206561018408165135037261)
                  ·
                    refine ⟨827460381903061925638973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2206561018408165135037261 827460381903061925638973)
                    ·
                      rfl

theorem cell22_2417210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 3, 3].length) (baseStart_2417210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2417210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2417210 prefixEnd_2417210 := by exact prefixLift 2417210
  have htrace : WordTrace (prefixWord ++ tailWord_2417210) baseStart_2417210 baseEnd_2417210 := by
    simpa [prefixWord, tailWord_2417210, baseEnd_2417210] using wordTrace_append hprefix tailTrace_2417210
  have hstable : (prefixWord ++ tailWord_2417210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417210).length < 2 ^ (prefixWord ++ tailWord_2417210).sum := by decide
  have hdescent : baseEnd_2417210 < baseStart_2417210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417246 : List Nat := [4, 4, 1, 2, 2, 1, 8]
def baseStart_2417246 : Nat := 118140960795 + 2417246 * 2 ^ 59
def prefixEnd_2417246 : Nat := 4983230072969 + 3 ^ 40 * 2417246 * 2
def baseEnd_2417246 : Nat := 30647137238472956731069

theorem tailTrace_2417246 : CollatzResearch.WordTrace tailWord_2417246 prefixEnd_2417246 30647137238472956731069 := by
  unfold tailWord_2417246
  simp only [CollatzResearch.WordTrace]
  refine ⟨11020525575092256199326949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58776136400492033063077061 11020525575092256199326949)
  ·
    refine ⟨2066348545329798037373803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11020525575092256199326949 2066348545329798037373803)
    ·
      refine ⟨3099522817994697056060705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2066348545329798037373803 3099522817994697056060705)
      ·
        refine ⟨2324642113496022792045529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3099522817994697056060705 2324642113496022792045529)
        ·
          refine ⟨1743481585122017094034147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2324642113496022792045529 1743481585122017094034147)
          ·
            refine ⟨2615222377683025641051221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1743481585122017094034147 2615222377683025641051221)
            ·
              refine ⟨30647137238472956731069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2615222377683025641051221 30647137238472956731069)
              ·
                rfl

theorem cell22_2417246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 8].length) (baseStart_2417246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2417246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2417246 prefixEnd_2417246 := by exact prefixLift 2417246
  have htrace : WordTrace (prefixWord ++ tailWord_2417246) baseStart_2417246 baseEnd_2417246 := by
    simpa [prefixWord, tailWord_2417246, baseEnd_2417246] using wordTrace_append hprefix tailTrace_2417246
  have hstable : (prefixWord ++ tailWord_2417246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417246).length < 2 ^ (prefixWord ++ tailWord_2417246).sum := by decide
  have hdescent : baseEnd_2417246 < baseStart_2417246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417261 : List Nat := [1, 5, 1, 1, 3, 2, 3, 2, 1, 3]
def baseStart_2417261 : Nat := 118140960795 + 2417261 * 2 ^ 59
def prefixEnd_2417261 : Nat := 4983230072969 + 3 ^ 40 * 2417261 * 2
def baseEnd_2417261 : Nat := 827477840245314792613817

theorem tailTrace_2417261 : CollatzResearch.WordTrace tailWord_2417261 prefixEnd_2417261 827477840245314792613817 := by
  unfold tailWord_2417261
  simp only [CollatzResearch.WordTrace]
  refine ⟨88164751695683707156411637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58776501130455804770941091 88164751695683707156411637)
  ·
    refine ⟨8265445471470347545913591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88164751695683707156411637 8265445471470347545913591)
    ·
      refine ⟨12398168207205521318870387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8265445471470347545913591 12398168207205521318870387)
      ·
        refine ⟨18597252310808281978305581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12398168207205521318870387 18597252310808281978305581)
        ·
          refine ⟨6973969616553105741864593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18597252310808281978305581 6973969616553105741864593)
          ·
            refine ⟨5230477212414829306398445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6973969616553105741864593 5230477212414829306398445)
            ·
              refine ⟨1961428954655560989899417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5230477212414829306398445 1961428954655560989899417)
              ·
                refine ⟨1471071715991670742424563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1961428954655560989899417 1471071715991670742424563)
                ·
                  refine ⟨2206607573987506113636845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1471071715991670742424563 2206607573987506113636845)
                  ·
                    refine ⟨827477840245314792613817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2206607573987506113636845 827477840245314792613817)
                    ·
                      rfl

theorem cell22_2417261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_2417261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2417261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2417261 prefixEnd_2417261 := by exact prefixLift 2417261
  have htrace : WordTrace (prefixWord ++ tailWord_2417261) baseStart_2417261 baseEnd_2417261 := by
    simpa [prefixWord, tailWord_2417261, baseEnd_2417261] using wordTrace_append hprefix tailTrace_2417261
  have hstable : (prefixWord ++ tailWord_2417261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417261).length < 2 ^ (prefixWord ++ tailWord_2417261).sum := by decide
  have hdescent : baseEnd_2417261 < baseStart_2417261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417313 : List Nat := [1, 2, 3, 3, 13]
def baseStart_2417313 : Nat := 118140960795 + 2417313 * 2 ^ 59
def prefixEnd_2417313 : Nat := 4983230072969 + 3 ^ 40 * 2417313 * 2
def baseEnd_2417313 : Nat := 3405331855588493787299

theorem tailTrace_2417313 : CollatzResearch.WordTrace tailWord_2417313 prefixEnd_2417313 3405331855588493787299 := by
  unfold tailWord_2417313
  simp only [CollatzResearch.WordTrace]
  refine ⟨88166648291495320037304593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58777765527663546691536395 88166648291495320037304593)
  ·
    refine ⟨66124986218621490027978445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88166648291495320037304593 66124986218621490027978445)
    ·
      refine ⟨24796869831983058760491917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66124986218621490027978445 24796869831983058760491917)
      ·
        refine ⟨9298826186993647035184469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24796869831983058760491917 9298826186993647035184469)
        ·
          refine ⟨3405331855588493787299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 9298826186993647035184469 3405331855588493787299)
          ·
            rfl

theorem cell22_2417313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 13].length) (baseStart_2417313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2417313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2417313 prefixEnd_2417313 := by exact prefixLift 2417313
  have htrace : WordTrace (prefixWord ++ tailWord_2417313) baseStart_2417313 baseEnd_2417313 := by
    simpa [prefixWord, tailWord_2417313, baseEnd_2417313] using wordTrace_append hprefix tailTrace_2417313
  have hstable : (prefixWord ++ tailWord_2417313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417313).length < 2 ^ (prefixWord ++ tailWord_2417313).sum := by decide
  have hdescent : baseEnd_2417313 < baseStart_2417313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417328 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 2, 7]
def baseStart_2417328 : Nat := 118140960795 + 2417328 * 2 ^ 59
def prefixEnd_2417328 : Nat := 4983230072969 + 3 ^ 40 * 2417328 * 2
def baseEnd_2417328 : Nat := 827500775714548951188611

theorem tailTrace_2417328 : CollatzResearch.WordTrace tailWord_2417328 prefixEnd_2417328 827500775714548951188611 := by
  unfold tailWord_2417328
  simp only [CollatzResearch.WordTrace]
  refine ⟨44083597693220488799550319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58778130257627318399400425 44083597693220488799550319)
  ·
    refine ⟨66125396539830733199325479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44083597693220488799550319 66125396539830733199325479)
    ·
      refine ⟨99188094809746099798988219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66125396539830733199325479 99188094809746099798988219)
      ·
        refine ⟨148782142214619149698482329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99188094809746099798988219 148782142214619149698482329)
        ·
          refine ⟨111586606660964362273861747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148782142214619149698482329 111586606660964362273861747)
          ·
            refine ⟨167379909991446543410792621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111586606660964362273861747 167379909991446543410792621)
            ·
              refine ⟨62767466246792453779047233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 167379909991446543410792621 62767466246792453779047233)
              ·
                refine ⟨47075599685094340334285425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62767466246792453779047233 47075599685094340334285425)
                ·
                  refine ⟨35306699763820755250714069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47075599685094340334285425 35306699763820755250714069)
                  ·
                    refine ⟨827500775714548951188611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35306699763820755250714069 827500775714548951188611)
                    ·
                      rfl

theorem cell22_2417328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 2, 7].length) (baseStart_2417328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2417328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2417328 prefixEnd_2417328 := by exact prefixLift 2417328
  have htrace : WordTrace (prefixWord ++ tailWord_2417328) baseStart_2417328 baseEnd_2417328 := by
    simpa [prefixWord, tailWord_2417328, baseEnd_2417328] using wordTrace_append hprefix tailTrace_2417328
  have hstable : (prefixWord ++ tailWord_2417328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417328).length < 2 ^ (prefixWord ++ tailWord_2417328).sum := by decide
  have hdescent : baseEnd_2417328 < baseStart_2417328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417375 : List Nat := [1, 1, 2, 3, 2, 4, 1, 1, 7]
def baseStart_2417375 : Nat := 118140960795 + 2417375 * 2 ^ 59
def prefixEnd_2417375 : Nat := 4983230072969 + 3 ^ 40 * 2417375 * 2
def baseEnd_2417375 : Nat := 275838954925018831754489

theorem tailTrace_2417375 : CollatzResearch.WordTrace tailWord_2417375 prefixEnd_2417375 275838954925018831754489 := by
  unfold tailWord_2417375
  simp only [CollatzResearch.WordTrace]
  refine ⟨88168909617270704626061579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58779273078180469750707719 88168909617270704626061579)
  ·
    refine ⟨132253364425906056939092369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88168909617270704626061579 132253364425906056939092369)
    ·
      refine ⟨99190023319429542704319277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132253364425906056939092369 99190023319429542704319277)
      ·
        refine ⟨37196258744786078514119729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99190023319429542704319277 37196258744786078514119729)
        ·
          refine ⟨27897194058589558885589797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37196258744786078514119729 27897194058589558885589797)
          ·
            refine ⟨5230723885985542291048087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27897194058589558885589797 5230723885985542291048087)
            ·
              refine ⟨7846085828978313436572131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5230723885985542291048087 7846085828978313436572131)
              ·
                refine ⟨11769128743467470154858197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7846085828978313436572131 11769128743467470154858197)
                ·
                  refine ⟨275838954925018831754489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11769128743467470154858197 275838954925018831754489)
                  ·
                    rfl

theorem cell22_2417375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 7].length) (baseStart_2417375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2417375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2417375 prefixEnd_2417375 := by exact prefixLift 2417375
  have htrace : WordTrace (prefixWord ++ tailWord_2417375) baseStart_2417375 baseEnd_2417375 := by
    simpa [prefixWord, tailWord_2417375, baseEnd_2417375] using wordTrace_append hprefix tailTrace_2417375
  have hstable : (prefixWord ++ tailWord_2417375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417375).length < 2 ^ (prefixWord ++ tailWord_2417375).sum := by decide
  have hdescent : baseEnd_2417375 < baseStart_2417375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417379 : List Nat := [1, 1, 1, 7, 1, 2, 2, 1, 3, 3]
def baseStart_2417379 : Nat := 118140960795 + 2417379 * 2 ^ 59
def prefixEnd_2417379 : Nat := 4983230072969 + 3 ^ 40 * 2417379 * 2
def baseEnd_2417379 : Nat := 827518234056801818163455

theorem tailTrace_2417379 : CollatzResearch.WordTrace tailWord_2417379 prefixEnd_2417379 827518234056801818163455 := by
  unfold tailWord_2417379
  simp only [CollatzResearch.WordTrace]
  refine ⟨88169055509256213309207191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58779370339504142206138127 88169055509256213309207191)
  ·
    refine ⟨132253583263884319963810787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88169055509256213309207191 132253583263884319963810787)
    ·
      refine ⟨198380374895826479945716181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132253583263884319963810787 198380374895826479945716181)
      ·
        refine ⟨4649540036620933123727723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 198380374895826479945716181 4649540036620933123727723)
        ·
          refine ⟨6974310054931399685591585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4649540036620933123727723 6974310054931399685591585)
          ·
            refine ⟨5230732541198549764193689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6974310054931399685591585 5230732541198549764193689)
            ·
              refine ⟨3923049405898912323145267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5230732541198549764193689 3923049405898912323145267)
              ·
                refine ⟨5884574108848368484717901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3923049405898912323145267 5884574108848368484717901)
                ·
                  refine ⟨2206715290818138181769213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5884574108848368484717901 2206715290818138181769213)
                  ·
                    refine ⟨827518234056801818163455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2206715290818138181769213 827518234056801818163455)
                    ·
                      rfl

theorem cell22_2417379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 3, 3].length) (baseStart_2417379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2417379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2417379 prefixEnd_2417379 := by exact prefixLift 2417379
  have htrace : WordTrace (prefixWord ++ tailWord_2417379) baseStart_2417379 baseEnd_2417379 := by
    simpa [prefixWord, tailWord_2417379, baseEnd_2417379] using wordTrace_append hprefix tailTrace_2417379
  have hstable : (prefixWord ++ tailWord_2417379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417379).length < 2 ^ (prefixWord ++ tailWord_2417379).sum := by decide
  have hdescent : baseEnd_2417379 < baseStart_2417379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417392 : List Nat := [2, 1, 1, 1, 3, 1, 7, 1, 5]
def baseStart_2417392 : Nat := 118140960795 + 2417392 * 2 ^ 59
def prefixEnd_2417392 : Nat := 4983230072969 + 3 ^ 40 * 2417392 * 2
def baseEnd_2417392 : Nat := 275840894740824705862805

theorem tailTrace_2417392 : CollatzResearch.WordTrace tailWord_2417392 prefixEnd_2417392 275840894740824705862805 := by
  unfold tailWord_2417392
  simp only [CollatzResearch.WordTrace]
  refine ⟨44084764829104558264715215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58779686438806077686286953 44084764829104558264715215)
  ·
    refine ⟨66127147243656837397072823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44084764829104558264715215 66127147243656837397072823)
    ·
      refine ⟨99190720865485256095609235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66127147243656837397072823 99190720865485256095609235)
      ·
        refine ⟨148786081298227884143413853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99190720865485256095609235 148786081298227884143413853)
        ·
          refine ⟨55794780486835456553780195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148786081298227884143413853 55794780486835456553780195)
          ·
            refine ⟨83692170730253184830670293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55794780486835456553780195 83692170730253184830670293)
            ·
              refine ⟨1961535251490309019468835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 83692170730253184830670293 1961535251490309019468835)
              ·
                refine ⟨2942302877235463529203253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1961535251490309019468835 2942302877235463529203253)
                ·
                  refine ⟨275840894740824705862805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2942302877235463529203253 275840894740824705862805)
                  ·
                    rfl

theorem cell22_2417392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 1, 5].length) (baseStart_2417392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2417392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2417392 prefixEnd_2417392 := by exact prefixLift 2417392
  have htrace : WordTrace (prefixWord ++ tailWord_2417392) baseStart_2417392 baseEnd_2417392 := by
    simpa [prefixWord, tailWord_2417392, baseEnd_2417392] using wordTrace_append hprefix tailTrace_2417392
  have hstable : (prefixWord ++ tailWord_2417392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417392).length < 2 ^ (prefixWord ++ tailWord_2417392).sum := by decide
  have hdescent : baseEnd_2417392 < baseStart_2417392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417469 : List Nat := [1, 4, 1, 4, 2, 1, 1, 2, 1, 5]
def baseStart_2417469 : Nat := 118140960795 + 2417469 * 2 ^ 59
def prefixEnd_2417469 : Nat := 4983230072969 + 3 ^ 40 * 2417469 * 2
def baseEnd_2417469 : Nat := 827549042896071583413179

theorem tailTrace_2417469 : CollatzResearch.WordTrace tailWord_2417469 prefixEnd_2417469 827549042896071583413179 := by
  unfold tailWord_2417469
  simp only [CollatzResearch.WordTrace]
  refine ⟨88172338078930158679983461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58781558719286772453322307 88172338078930158679983461)
  ·
    refine ⟨16532313389799404752496899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88172338078930158679983461 16532313389799404752496899)
    ·
      refine ⟨24798470084699107128745349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16532313389799404752496899 24798470084699107128745349)
      ·
        refine ⟨4649713140881082586639753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24798470084699107128745349 4649713140881082586639753)
        ·
          refine ⟨3487284855660811939979815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4649713140881082586639753 3487284855660811939979815)
          ·
            refine ⟨5230927283491217909969723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3487284855660811939979815 5230927283491217909969723)
            ·
              refine ⟨7846390925236826864954585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5230927283491217909969723 7846390925236826864954585)
              ·
                refine ⟨5884793193927620148715939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7846390925236826864954585 5884793193927620148715939)
                ·
                  refine ⟨8827189790891430223073909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5884793193927620148715939 8827189790891430223073909)
                  ·
                    refine ⟨827549042896071583413179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8827189790891430223073909 827549042896071583413179)
                    ·
                      rfl

theorem cell22_2417469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_2417469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2417469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2417469 prefixEnd_2417469 := by exact prefixLift 2417469
  have htrace : WordTrace (prefixWord ++ tailWord_2417469) baseStart_2417469 baseEnd_2417469 := by
    simpa [prefixWord, tailWord_2417469, baseEnd_2417469] using wordTrace_append hprefix tailTrace_2417469
  have hstable : (prefixWord ++ tailWord_2417469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417469).length < 2 ^ (prefixWord ++ tailWord_2417469).sum := by decide
  have hdescent : baseEnd_2417469 < baseStart_2417469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417473 : List Nat := [1, 2, 5, 3, 1, 1, 3, 1, 1, 4]
def baseStart_2417473 : Nat := 118140960795 + 2417473 * 2 ^ 59
def prefixEnd_2417473 : Nat := 4983230072969 + 3 ^ 40 * 2417473 * 2
def baseEnd_2417473 : Nat := 827550412177816906313167

theorem tailTrace_2417473 : CollatzResearch.WordTrace tailWord_2417473 prefixEnd_2417473 827550412177816906313167 := by
  unfold tailWord_2417473
  simp only [CollatzResearch.WordTrace]
  refine ⟨88172483970915667363129073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58781655980610444908752715 88172483970915667363129073)
  ·
    refine ⟨66129362978186750522346805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88172483970915667363129073 66129362978186750522346805)
    ·
      refine ⟨6199627779205007861470013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66129362978186750522346805 6199627779205007861470013)
      ·
        refine ⟨2324860417201877948051255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6199627779205007861470013 2324860417201877948051255)
        ·
          refine ⟨3487290625802816922076883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2324860417201877948051255 3487290625802816922076883)
          ·
            refine ⟨5230935938704225383115325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3487290625802816922076883 5230935938704225383115325)
            ·
              refine ⟨1961600977014084518668247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5230935938704225383115325 1961600977014084518668247)
              ·
                refine ⟨2942401465521126778002371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1961600977014084518668247 2942401465521126778002371)
                ·
                  refine ⟨4413602198281690167003557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2942401465521126778002371 4413602198281690167003557)
                  ·
                    refine ⟨827550412177816906313167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4413602198281690167003557 827550412177816906313167)
                    ·
                      rfl

theorem cell22_2417473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_2417473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2417473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2417473 prefixEnd_2417473 := by exact prefixLift 2417473
  have htrace : WordTrace (prefixWord ++ tailWord_2417473) baseStart_2417473 baseEnd_2417473 := by
    simpa [prefixWord, tailWord_2417473, baseEnd_2417473] using wordTrace_append hprefix tailTrace_2417473
  have hstable : (prefixWord ++ tailWord_2417473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417473).length < 2 ^ (prefixWord ++ tailWord_2417473).sum := by decide
  have hdescent : baseEnd_2417473 < baseStart_2417473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417518 : List Nat := [4, 1, 2, 3, 3, 1, 1, 1, 2, 4]
def baseStart_2417518 : Nat := 118140960795 + 2417518 * 2 ^ 59
def prefixEnd_2417518 : Nat := 4983230072969 + 3 ^ 40 * 2417518 * 2
def baseEnd_2417518 : Nat := 827565816597451788938029

theorem tailTrace_2417518 : CollatzResearch.WordTrace tailWord_2417518 prefixEnd_2417518 827565816597451788938029 := by
  unfold tailWord_2417518
  simp only [CollatzResearch.WordTrace]
  refine ⟨11021765656969080006064651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58782750170501760032344805 11021765656969080006064651)
  ·
    refine ⟨16532648485453620009096977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11021765656969080006064651 16532648485453620009096977)
    ·
      refine ⟨12399486364090215006822733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16532648485453620009096977 12399486364090215006822733)
      ·
        refine ⟨4649807386533830627558525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12399486364090215006822733 4649807386533830627558525)
        ·
          refine ⟨1743677769950186485334447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4649807386533830627558525 1743677769950186485334447)
          ·
            refine ⟨2615516654925279728001671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1743677769950186485334447 2615516654925279728001671)
            ·
              refine ⟨3923274982387919592002507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2615516654925279728001671 3923274982387919592002507)
              ·
                refine ⟨5884912473581879388003761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3923274982387919592002507 5884912473581879388003761)
                ·
                  refine ⟨4413684355186409541002821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5884912473581879388003761 4413684355186409541002821)
                  ·
                    refine ⟨827565816597451788938029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4413684355186409541002821 827565816597451788938029)
                    ·
                      rfl

theorem cell22_2417518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_2417518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2417518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2417518 prefixEnd_2417518 := by exact prefixLift 2417518
  have htrace : WordTrace (prefixWord ++ tailWord_2417518) baseStart_2417518 baseEnd_2417518 := by
    simpa [prefixWord, tailWord_2417518, baseEnd_2417518] using wordTrace_append hprefix tailTrace_2417518
  have hstable : (prefixWord ++ tailWord_2417518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417518).length < 2 ^ (prefixWord ++ tailWord_2417518).sum := by decide
  have hdescent : baseEnd_2417518 < baseStart_2417518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417544 : List Nat := [2, 1, 3, 3, 2, 1, 3, 2, 5]
def baseStart_2417544 : Nat := 118140960795 + 2417544 * 2 ^ 59
def prefixEnd_2417544 : Nat := 4983230072969 + 3 ^ 40 * 2417544 * 2
def baseEnd_2417544 : Nat := 275858238976265462595983

theorem tailTrace_2417544 : CollatzResearch.WordTrace tailWord_2417544 prefixEnd_2417544 275858238976265462595983 := by
  unfold tailWord_2417544
  simp only [CollatzResearch.WordTrace]
  refine ⟨44087536776829223244481843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58783382369105630992642457 44087536776829223244481843)
  ·
    refine ⟨66131305165243834866722765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44087536776829223244481843 66131305165243834866722765)
    ·
      refine ⟨24799239436966438075021037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66131305165243834866722765 24799239436966438075021037)
      ·
        refine ⟨9299714788862414278132889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24799239436966438075021037 9299714788862414278132889)
        ·
          refine ⟨6974786091646810708599667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9299714788862414278132889 6974786091646810708599667)
          ·
            refine ⟨10462179137470216062899501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6974786091646810708599667 10462179137470216062899501)
            ·
              refine ⟨3923317176551331023587313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10462179137470216062899501 3923317176551331023587313)
              ·
                refine ⟨2942487882413498267690485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3923317176551331023587313 2942487882413498267690485)
                ·
                  refine ⟨275858238976265462595983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2942487882413498267690485 275858238976265462595983)
                  ·
                    rfl

theorem cell22_2417544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2, 5].length) (baseStart_2417544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2417544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2417544 prefixEnd_2417544 := by exact prefixLift 2417544
  have htrace : WordTrace (prefixWord ++ tailWord_2417544) baseStart_2417544 baseEnd_2417544 := by
    simpa [prefixWord, tailWord_2417544, baseEnd_2417544] using wordTrace_append hprefix tailTrace_2417544
  have hstable : (prefixWord ++ tailWord_2417544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417544).length < 2 ^ (prefixWord ++ tailWord_2417544).sum := by decide
  have hdescent : baseEnd_2417544 < baseStart_2417544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417572 : List Nat := [2, 3, 1, 2, 1, 2, 1, 4, 6]
def baseStart_2417572 : Nat := 118140960795 + 2417572 * 2 ^ 59
def prefixEnd_2417572 : Nat := 4983230072969 + 3 ^ 40 * 2417572 * 2
def baseEnd_2417572 : Nat := 275861433967004549362621

theorem tailTrace_2417572 : CollatzResearch.WordTrace tailWord_2417572 prefixEnd_2417572 275861433967004549362621 := by
  unfold tailWord_2417572
  simp only [CollatzResearch.WordTrace]
  refine ⟨44088047398778503635491485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58784063198371338180655313 44088047398778503635491485)
  ·
    refine ⟨16533017774541938863309307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44088047398778503635491485 16533017774541938863309307)
    ·
      refine ⟨24799526661812908294963961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16533017774541938863309307 24799526661812908294963961)
      ·
        refine ⟨18599644996359681221222971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24799526661812908294963961 18599644996359681221222971)
        ·
          refine ⟨27899467494539521831834457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18599644996359681221222971 27899467494539521831834457)
          ·
            refine ⟨20924600620904641373875843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27899467494539521831834457 20924600620904641373875843)
            ·
              refine ⟨31386900931356962060813765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20924600620904641373875843 31386900931356962060813765)
              ·
                refine ⟨5885043924629430386402581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31386900931356962060813765 5885043924629430386402581)
                ·
                  refine ⟨275861433967004549362621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5885043924629430386402581 275861433967004549362621)
                  ·
                    rfl

theorem cell22_2417572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_2417572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2417572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2417572 prefixEnd_2417572 := by exact prefixLift 2417572
  have htrace : WordTrace (prefixWord ++ tailWord_2417572) baseStart_2417572 baseEnd_2417572 := by
    simpa [prefixWord, tailWord_2417572, baseEnd_2417572] using wordTrace_append hprefix tailTrace_2417572
  have hstable : (prefixWord ++ tailWord_2417572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417572).length < 2 ^ (prefixWord ++ tailWord_2417572).sum := by decide
  have hdescent : baseEnd_2417572 < baseStart_2417572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417617 : List Nat := [1, 2, 2, 1, 2, 1, 6, 7]
def baseStart_2417617 : Nat := 118140960795 + 2417617 * 2 ^ 59
def prefixEnd_2417617 : Nat := 4983230072969 + 3 ^ 40 * 2417617 * 2
def baseEnd_2417617 : Nat := 91955522924516503412525

theorem tailTrace_2417617 : CollatzResearch.WordTrace tailWord_2417617 prefixEnd_2417617 91955522924516503412525 := by
  unfold tailWord_2417617
  simp only [CollatzResearch.WordTrace]
  refine ⟨88177736082393979956371105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58785157388262653304247403 88177736082393979956371105)
  ·
    refine ⟨66133302061795484967278329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88177736082393979956371105 66133302061795484967278329)
    ·
      refine ⟨49599976546346613725458747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66133302061795484967278329 49599976546346613725458747)
      ·
        refine ⟨74399964819519920588188121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49599976546346613725458747 74399964819519920588188121)
        ·
          refine ⟨55799973614639940441141091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74399964819519920588188121 55799973614639940441141091)
          ·
            refine ⟨83699960421959910661711637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55799973614639940441141091 83699960421959910661711637)
            ·
              refine ⟨3923435644779370812267733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 83699960421959910661711637 3923435644779370812267733)
              ·
                refine ⟨91955522924516503412525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3923435644779370812267733 91955522924516503412525)
                ·
                  rfl

theorem cell22_2417617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 7].length) (baseStart_2417617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2417617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2417617 prefixEnd_2417617 := by exact prefixLift 2417617
  have htrace : WordTrace (prefixWord ++ tailWord_2417617) baseStart_2417617 baseEnd_2417617 := by
    simpa [prefixWord, tailWord_2417617, baseEnd_2417617] using wordTrace_append hprefix tailTrace_2417617
  have hstable : (prefixWord ++ tailWord_2417617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417617).length < 2 ^ (prefixWord ++ tailWord_2417617).sum := by decide
  have hdescent : baseEnd_2417617 < baseStart_2417617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417700 : List Nat := [2, 3, 1, 4, 1, 2, 2, 3, 1, 3]
def baseStart_2417700 : Nat := 118140960795 + 2417700 * 2 ^ 59
def prefixEnd_2417700 : Nat := 4983230072969 + 3 ^ 40 * 2417700 * 2
def baseEnd_2417700 : Nat := 827628118916863980887471

theorem tailTrace_2417700 : CollatzResearch.WordTrace tailWord_2417700 prefixEnd_2417700 827628118916863980887471 := by
  unfold tailWord_2417700
  simp only [CollatzResearch.WordTrace]
  refine ⟨44090381670546642565821277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58787175560728856754428369 44090381670546642565821277)
  ·
    refine ⟨16533893126454990962182979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44090381670546642565821277 16533893126454990962182979)
    ·
      refine ⟨24800839689682486443274469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16533893126454990962182979 24800839689682486443274469)
      ·
        refine ⟨4650157441815466208113963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24800839689682486443274469 4650157441815466208113963)
        ·
          refine ⟨6975236162723199312170945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4650157441815466208113963 6975236162723199312170945)
          ·
            refine ⟨5231427122042399484128209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6975236162723199312170945 5231427122042399484128209)
            ·
              refine ⟨3923570341531799613096157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5231427122042399484128209 3923570341531799613096157)
              ·
                refine ⟨1471338878074424854911059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3923570341531799613096157 1471338878074424854911059)
                ·
                  refine ⟨2207008317111637282366589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1471338878074424854911059 2207008317111637282366589)
                  ·
                    refine ⟨827628118916863980887471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2207008317111637282366589 827628118916863980887471)
                    ·
                      rfl

theorem cell22_2417700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 3, 1, 3].length) (baseStart_2417700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2417700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2417700 prefixEnd_2417700 := by exact prefixLift 2417700
  have htrace : WordTrace (prefixWord ++ tailWord_2417700) baseStart_2417700 baseEnd_2417700 := by
    simpa [prefixWord, tailWord_2417700, baseEnd_2417700] using wordTrace_append hprefix tailTrace_2417700
  have hstable : (prefixWord ++ tailWord_2417700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417700).length < 2 ^ (prefixWord ++ tailWord_2417700).sum := by decide
  have hdescent : baseEnd_2417700 < baseStart_2417700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417707 : List Nat := [1, 1, 1, 1, 2, 1, 5, 2, 8]
def baseStart_2417707 : Nat := 118140960795 + 2417707 * 2 ^ 59
def prefixEnd_2417707 : Nat := 4983230072969 + 3 ^ 40 * 2417707 * 2
def baseEnd_2417707 : Nat := 275876838386639431987483

theorem tailTrace_2417707 : CollatzResearch.WordTrace tailWord_2417707 prefixEnd_2417707 275876838386639431987483 := by
  unfold tailWord_2417707
  simp only [CollatzResearch.WordTrace]
  refine ⟨88181018652067925327147375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58787345768045283551431583 88181018652067925327147375)
  ·
    refine ⟨132271527978101887990721063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88181018652067925327147375 132271527978101887990721063)
    ·
      refine ⟨198407291967152831986081595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132271527978101887990721063 198407291967152831986081595)
      ·
        refine ⟨297610937950729247979122393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198407291967152831986081595 297610937950729247979122393)
        ·
          refine ⟨223208203463046935984341795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 297610937950729247979122393 223208203463046935984341795)
          ·
            refine ⟨334812305194570403976512693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223208203463046935984341795 334812305194570403976512693)
            ·
              refine ⟨31388653611990975372798065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 334812305194570403976512693 31388653611990975372798065)
              ·
                refine ⟨23541490208993231529598549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31388653611990975372798065 23541490208993231529598549)
                ·
                  refine ⟨275876838386639431987483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23541490208993231529598549 275876838386639431987483)
                  ·
                    rfl

theorem cell22_2417707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 8].length) (baseStart_2417707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2417707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2417707 prefixEnd_2417707 := by exact prefixLift 2417707
  have htrace : WordTrace (prefixWord ++ tailWord_2417707) baseStart_2417707 baseEnd_2417707 := by
    simpa [prefixWord, tailWord_2417707, baseEnd_2417707] using wordTrace_append hprefix tailTrace_2417707
  have hstable : (prefixWord ++ tailWord_2417707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417707).length < 2 ^ (prefixWord ++ tailWord_2417707).sum := by decide
  have hdescent : baseEnd_2417707 < baseStart_2417707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417724 : List Nat := [2, 2, 2, 2, 2, 2, 1, 3, 6]
def baseStart_2417724 : Nat := 118140960795 + 2417724 * 2 ^ 59
def prefixEnd_2417724 : Nat := 4983230072969 + 3 ^ 40 * 2417724 * 2
def baseEnd_2417724 : Nat := 275878778202445306095799

theorem tailTrace_2417724 : CollatzResearch.WordTrace tailWord_2417724 prefixEnd_2417724 275878778202445306095799 := by
  unfold tailWord_2417724
  simp only [CollatzResearch.WordTrace]
  refine ⟨44090819346503168615258113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58787759128670891487010817 44090819346503168615258113)
  ·
    refine ⟨33068114509877376461443585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44090819346503168615258113 33068114509877376461443585)
    ·
      refine ⟨24801085882408032346082689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33068114509877376461443585 24801085882408032346082689)
      ·
        refine ⟨18600814411806024259562017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24801085882408032346082689 18600814411806024259562017)
        ·
          refine ⟨13950610808854518194671513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18600814411806024259562017 13950610808854518194671513)
          ·
            refine ⟨10462958106640888646003635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13950610808854518194671513 10462958106640888646003635)
            ·
              refine ⟨15694437159961332969005453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10462958106640888646003635 15694437159961332969005453)
              ·
                refine ⟨5885413934985499863377045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15694437159961332969005453 5885413934985499863377045)
                ·
                  refine ⟨275878778202445306095799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5885413934985499863377045 275878778202445306095799)
                  ·
                    rfl

theorem cell22_2417724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 6].length) (baseStart_2417724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2417724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2417724 prefixEnd_2417724 := by exact prefixLift 2417724
  have htrace : WordTrace (prefixWord ++ tailWord_2417724) baseStart_2417724 baseEnd_2417724 := by
    simpa [prefixWord, tailWord_2417724, baseEnd_2417724] using wordTrace_append hprefix tailTrace_2417724
  have hstable : (prefixWord ++ tailWord_2417724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417724).length < 2 ^ (prefixWord ++ tailWord_2417724).sum := by decide
  have hdescent : baseEnd_2417724 < baseStart_2417724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417739 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 8, 3]
def baseStart_2417739 : Nat := 118140960795 + 2417739 * 2 ^ 59
def prefixEnd_2417739 : Nat := 4983230072969 + 3 ^ 40 * 2417739 * 2
def baseEnd_2417739 : Nat := 827641469413880879162351

theorem tailTrace_2417739 : CollatzResearch.WordTrace tailWord_2417739 prefixEnd_2417739 827641469413880879162351 := by
  unfold tailWord_2417739
  simp only [CollatzResearch.WordTrace]
  refine ⟨88182185787951994792312271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58788123858634663194874847 88182185787951994792312271)
  ·
    refine ⟨132273278681927992188468407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88182185787951994792312271 132273278681927992188468407)
    ·
      refine ⟨198409918022891988282702611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132273278681927992188468407 198409918022891988282702611)
      ·
        refine ⟨297614877034337982424053917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198409918022891988282702611 297614877034337982424053917)
        ·
          refine ⟨111605578887876743409020219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 297614877034337982424053917 111605578887876743409020219)
          ·
            refine ⟨167408368331815115113530329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111605578887876743409020219 167408368331815115113530329)
            ·
              refine ⟨125556276248861336335147747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167408368331815115113530329 125556276248861336335147747)
              ·
                refine ⟨188334414373292004502721621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125556276248861336335147747 188334414373292004502721621)
                ·
                  refine ⟨2207043918437015677766269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 188334414373292004502721621 2207043918437015677766269)
                  ·
                    refine ⟨827641469413880879162351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2207043918437015677766269 827641469413880879162351)
                    ·
                      rfl

theorem cell22_2417739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 8, 3].length) (baseStart_2417739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2417739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2417739 prefixEnd_2417739 := by exact prefixLift 2417739
  have htrace : WordTrace (prefixWord ++ tailWord_2417739) baseStart_2417739 baseEnd_2417739 := by
    simpa [prefixWord, tailWord_2417739, baseEnd_2417739] using wordTrace_append hprefix tailTrace_2417739
  have hstable : (prefixWord ++ tailWord_2417739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417739).length < 2 ^ (prefixWord ++ tailWord_2417739).sum := by decide
  have hdescent : baseEnd_2417739 < baseStart_2417739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417741 : List Nat := [1, 6, 1, 1, 1, 2, 2, 2, 6]
def baseStart_2417741 : Nat := 118140960795 + 2417741 * 2 ^ 59
def prefixEnd_2417741 : Nat := 4983230072969 + 3 ^ 40 * 2417741 * 2
def baseEnd_2417741 : Nat := 275880718018251180204115

theorem tailTrace_2417741 : CollatzResearch.WordTrace tailWord_2417741 prefixEnd_2417741 275880718018251180204115 := by
  unfold tailWord_2417741
  simp only [CollatzResearch.WordTrace]
  refine ⟨88182258733944749133885077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58788172489296499422590051 88182258733944749133885077)
  ·
    refine ⟨4133543378153660115650863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 88182258733944749133885077 4133543378153660115650863)
    ·
      refine ⟨6200315067230490173476295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4133543378153660115650863 6200315067230490173476295)
      ·
        refine ⟨9300472600845735260214443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6200315067230490173476295 9300472600845735260214443)
        ·
          refine ⟨13950708901268602890321665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9300472600845735260214443 13950708901268602890321665)
          ·
            refine ⟨10463031675951452167741249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13950708901268602890321665 10463031675951452167741249)
            ·
              refine ⟨7847273756963589125805937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10463031675951452167741249 7847273756963589125805937)
              ·
                refine ⟨5885455317722691844354453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7847273756963589125805937 5885455317722691844354453)
                ·
                  refine ⟨275880718018251180204115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5885455317722691844354453 275880718018251180204115)
                  ·
                    rfl

theorem cell22_2417741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_2417741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2417741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2417741 prefixEnd_2417741 := by exact prefixLift 2417741
  have htrace : WordTrace (prefixWord ++ tailWord_2417741) baseStart_2417741 baseEnd_2417741 := by
    simpa [prefixWord, tailWord_2417741, baseEnd_2417741] using wordTrace_append hprefix tailTrace_2417741
  have hstable : (prefixWord ++ tailWord_2417741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417741).length < 2 ^ (prefixWord ++ tailWord_2417741).sum := by decide
  have hdescent : baseEnd_2417741 < baseStart_2417741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417756 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 6, 3]
def baseStart_2417756 : Nat := 118140960795 + 2417756 * 2 ^ 59
def prefixEnd_2417756 : Nat := 4983230072969 + 3 ^ 40 * 2417756 * 2
def baseEnd_2417756 : Nat := 827647288861298501487299

theorem tailTrace_2417756 : CollatzResearch.WordTrace tailWord_2417756 prefixEnd_2417756 827647288861298501487299 := by
  unfold tailWord_2417756
  simp only [CollatzResearch.WordTrace]
  refine ⟨44091402914445203347840561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58788537219260271130454081 44091402914445203347840561)
  ·
    refine ⟨33068552185833902510880421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44091402914445203347840561 33068552185833902510880421)
    ·
      refine ⟨6200353534843856720790079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33068552185833902510880421 6200353534843856720790079)
      ·
        refine ⟨9300530302265785081185119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6200353534843856720790079 9300530302265785081185119)
        ·
          refine ⟨13950795453398677621777679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9300530302265785081185119 13950795453398677621777679)
          ·
            refine ⟨20926193180098016432666519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13950795453398677621777679 20926193180098016432666519)
            ·
              refine ⟨31389289770147024648999779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20926193180098016432666519 31389289770147024648999779)
              ·
                refine ⟨47083934655220536973499669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31389289770147024648999779 47083934655220536973499669)
                ·
                  refine ⟨2207059436963462670632797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 47083934655220536973499669 2207059436963462670632797)
                  ·
                    refine ⟨827647288861298501487299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2207059436963462670632797 827647288861298501487299)
                    ·
                      rfl

theorem cell22_2417756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_2417756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2417756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2417756 prefixEnd_2417756 := by exact prefixLift 2417756
  have htrace : WordTrace (prefixWord ++ tailWord_2417756) baseStart_2417756 baseEnd_2417756 := by
    simpa [prefixWord, tailWord_2417756, baseEnd_2417756] using wordTrace_append hprefix tailTrace_2417756
  have hstable : (prefixWord ++ tailWord_2417756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417756).length < 2 ^ (prefixWord ++ tailWord_2417756).sum := by decide
  have hdescent : baseEnd_2417756 < baseStart_2417756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417769 : List Nat := [1, 2, 1, 1, 1, 8, 8]
def baseStart_2417769 : Nat := 118140960795 + 2417769 * 2 ^ 59
def prefixEnd_2417769 : Nat := 4983230072969 + 3 ^ 40 * 2417769 * 2
def baseEnd_2417769 : Nat := 30653768112110029663417

theorem tailTrace_2417769 : CollatzResearch.WordTrace tailWord_2417769 prefixEnd_2417769 30653768112110029663417 := by
  unfold tailWord_2417769
  simp only [CollatzResearch.WordTrace]
  refine ⟨88183279977843309915904361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58788853318562206610602907 88183279977843309915904361)
  ·
    refine ⟨66137459983382482436928271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88183279977843309915904361 66137459983382482436928271)
    ·
      refine ⟨99206189975073723655392407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66137459983382482436928271 99206189975073723655392407)
      ·
        refine ⟨148809284962610585483088611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99206189975073723655392407 148809284962610585483088611)
        ·
          refine ⟨223213927443915878224632917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148809284962610585483088611 223213927443915878224632917)
          ·
            refine ⟨2615788212233389197944917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 223213927443915878224632917 2615788212233389197944917)
            ·
              refine ⟨30653768112110029663417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2615788212233389197944917 30653768112110029663417)
              ·
                rfl

theorem cell22_2417769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 8].length) (baseStart_2417769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2417769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2417769 prefixEnd_2417769 := by exact prefixLift 2417769
  have htrace : WordTrace (prefixWord ++ tailWord_2417769) baseStart_2417769 baseEnd_2417769 := by
    simpa [prefixWord, tailWord_2417769, baseEnd_2417769] using wordTrace_append hprefix tailTrace_2417769
  have hstable : (prefixWord ++ tailWord_2417769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417769).length < 2 ^ (prefixWord ++ tailWord_2417769).sum := by decide
  have hdescent : baseEnd_2417769 < baseStart_2417769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417861 : List Nat := [1, 3, 1, 1, 1, 1, 3, 6, 1, 4]
def baseStart_2417861 : Nat := 118140960795 + 2417861 * 2 ^ 59
def prefixEnd_2417861 : Nat := 4983230072969 + 3 ^ 40 * 2417861 * 2
def baseEnd_2417861 : Nat := 827683232507113227611977

theorem tailTrace_2417861 : CollatzResearch.WordTrace tailWord_2417861 prefixEnd_2417861 827683232507113227611977 := by
  unfold tailWord_2417861
  simp only [CollatzResearch.WordTrace]
  refine ⟨88186635493510009628253437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58791090329006673085502291 88186635493510009628253437)
  ·
    refine ⟨33069988310066253610595039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88186635493510009628253437 33069988310066253610595039)
    ·
      refine ⟨49604982465099380415892559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33069988310066253610595039 49604982465099380415892559)
      ·
        refine ⟨74407473697649070623838839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49604982465099380415892559 74407473697649070623838839)
        ·
          refine ⟨111611210546473605935758259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74407473697649070623838839 111611210546473605935758259)
          ·
            refine ⟨167416815819710408903637389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111611210546473605935758259 167416815819710408903637389)
            ·
              refine ⟨62781305932391403338864021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 167416815819710408903637389 62781305932391403338864021)
              ·
                refine ⟨2942873715580847031509251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 62781305932391403338864021 2942873715580847031509251)
                ·
                  refine ⟨4414310573371270547263877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2942873715580847031509251 4414310573371270547263877)
                  ·
                    refine ⟨827683232507113227611977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4414310573371270547263877 827683232507113227611977)
                    ·
                      rfl

theorem cell22_2417861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6, 1, 4].length) (baseStart_2417861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2417861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2417861 prefixEnd_2417861 := by exact prefixLift 2417861
  have htrace : WordTrace (prefixWord ++ tailWord_2417861) baseStart_2417861 baseEnd_2417861 := by
    simpa [prefixWord, tailWord_2417861, baseEnd_2417861] using wordTrace_append hprefix tailTrace_2417861
  have hstable : (prefixWord ++ tailWord_2417861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417861).length < 2 ^ (prefixWord ++ tailWord_2417861).sum := by decide
  have hdescent : baseEnd_2417861 < baseStart_2417861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417893 : List Nat := [1, 3, 1, 4, 3, 1, 2, 1, 6]
def baseStart_2417893 : Nat := 118140960795 + 2417893 * 2 ^ 59
def prefixEnd_2417893 : Nat := 4983230072969 + 3 ^ 40 * 2417893 * 2
def baseEnd_2417893 : Nat := 275898062253691936937293

theorem tailTrace_2417893 : CollatzResearch.WordTrace tailWord_2417893 prefixEnd_2417893 275898062253691936937293 := by
  unfold tailWord_2417893
  simp only [CollatzResearch.WordTrace]
  refine ⟨88187802629394079093418333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58791868419596052728945555 88187802629394079093418333)
  ·
    refine ⟨33070425986022779660031875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88187802629394079093418333 33070425986022779660031875)
    ·
      refine ⟨49605638979034169490047813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33070425986022779660031875 49605638979034169490047813)
      ·
        refine ⟨9301057308568906779383965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49605638979034169490047813 9301057308568906779383965)
        ·
          refine ⟨3487896490713340042268987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9301057308568906779383965 3487896490713340042268987)
          ·
            refine ⟨5231844736070010063403481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3487896490713340042268987 5231844736070010063403481)
            ·
              refine ⟨3923883552052507547552611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5231844736070010063403481 3923883552052507547552611)
              ·
                refine ⟨5885825328078761321328917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3923883552052507547552611 5885825328078761321328917)
                ·
                  refine ⟨275898062253691936937293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5885825328078761321328917 275898062253691936937293)
                  ·
                    rfl

theorem cell22_2417893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 6].length) (baseStart_2417893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2417893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2417893 prefixEnd_2417893 := by exact prefixLift 2417893
  have htrace : WordTrace (prefixWord ++ tailWord_2417893) baseStart_2417893 baseEnd_2417893 := by
    simpa [prefixWord, tailWord_2417893, baseEnd_2417893] using wordTrace_append hprefix tailTrace_2417893
  have hstable : (prefixWord ++ tailWord_2417893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417893).length < 2 ^ (prefixWord ++ tailWord_2417893).sum := by decide
  have hdescent : baseEnd_2417893 < baseStart_2417893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417921 : List Nat := [1, 2, 4, 1, 1, 4, 1, 8]
def baseStart_2417921 : Nat := 118140960795 + 2417921 * 2 ^ 59
def prefixEnd_2417921 : Nat := 4983230072969 + 3 ^ 40 * 2417921 * 2
def baseEnd_2417921 : Nat := 91967085748143674567977

theorem tailTrace_2417921 : CollatzResearch.WordTrace tailWord_2417921 prefixEnd_2417921 91967085748143674567977 := by
  unfold tailWord_2417921
  simp only [CollatzResearch.WordTrace]
  refine ⟨88188823873292639875437617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58792549248861759916958411 88188823873292639875437617)
  ·
    refine ⟨66141617904969479906578213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88188823873292639875437617 66141617904969479906578213)
    ·
      refine ⟨12401553357181777482483415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66141617904969479906578213 12401553357181777482483415)
      ·
        refine ⟨18602330035772666223725123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12401553357181777482483415 18602330035772666223725123)
        ·
          refine ⟨27903495053658999335587685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18602330035772666223725123 27903495053658999335587685)
          ·
            refine ⟨5231905322561062375422691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27903495053658999335587685 5231905322561062375422691)
            ·
              refine ⟨7847857983841593563134037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5231905322561062375422691 7847857983841593563134037)
              ·
                refine ⟨91967085748143674567977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7847857983841593563134037 91967085748143674567977)
                ·
                  rfl

theorem cell22_2417921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 8].length) (baseStart_2417921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2417921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2417921 prefixEnd_2417921 := by exact prefixLift 2417921
  have htrace : WordTrace (prefixWord ++ tailWord_2417921) baseStart_2417921 baseEnd_2417921 := by
    simpa [prefixWord, tailWord_2417921, baseEnd_2417921] using wordTrace_append hprefix tailTrace_2417921
  have hstable : (prefixWord ++ tailWord_2417921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417921).length < 2 ^ (prefixWord ++ tailWord_2417921).sum := by decide
  have hdescent : baseEnd_2417921 < baseStart_2417921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418006 : List Nat := [5, 2, 3, 1, 2, 1, 1, 7]
def baseStart_2418006 : Nat := 118140960795 + 2418006 * 2 ^ 59
def prefixEnd_2418006 : Nat := 4983230072969 + 3 ^ 40 * 2418006 * 2
def baseEnd_2418006 : Nat := 91970318774486798081837

theorem tailTrace_2418006 : CollatzResearch.WordTrace tailWord_2418006 prefixEnd_2418006 91970318774486798081837 := by
  unfold tailWord_2418006
  simp only [CollatzResearch.WordTrace]
  refine ⟨5511995254874043712017617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58794616051989799594854581 5511995254874043712017617)
  ·
    refine ⟨4133996441155532784013213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5511995254874043712017617 4133996441155532784013213)
    ·
      refine ⟨1550248665433324794004955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4133996441155532784013213 1550248665433324794004955)
      ·
        refine ⟨2325372998149987191007433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1550248665433324794004955 2325372998149987191007433)
        ·
          refine ⟨1744029748612490393255575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2325372998149987191007433 1744029748612490393255575)
          ·
            refine ⟨2616044622918735589883363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1744029748612490393255575 2616044622918735589883363)
            ·
              refine ⟨3924066934378103384825045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2616044622918735589883363 3924066934378103384825045)
              ·
                refine ⟨91970318774486798081837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3924066934378103384825045 91970318774486798081837)
                ·
                  rfl

theorem cell22_2418006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_2418006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418006 prefixEnd_2418006 := by exact prefixLift 2418006
  have htrace : WordTrace (prefixWord ++ tailWord_2418006) baseStart_2418006 baseEnd_2418006 := by
    simpa [prefixWord, tailWord_2418006, baseEnd_2418006] using wordTrace_append hprefix tailTrace_2418006
  have hstable : (prefixWord ++ tailWord_2418006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418006).length < 2 ^ (prefixWord ++ tailWord_2418006).sum := by decide
  have hdescent : baseEnd_2418006 < baseStart_2418006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418028 : List Nat := [2, 2, 1, 1, 5, 2, 1, 2, 6]
def baseStart_2418028 : Nat := 118140960795 + 2418028 * 2 ^ 59
def prefixEnd_2418028 : Nat := 4983230072969 + 3 ^ 40 * 2418028 * 2
def baseEnd_2418028 : Nat := 275913466673326819562155

theorem tailTrace_2418028 : CollatzResearch.WordTrace tailWord_2418028 prefixEnd_2418028 275913466673326819562155 := by
  unfold tailWord_2418028
  simp only [CollatzResearch.WordTrace]
  refine ⟨44096363241952498574791369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58795150989269998099721825 44096363241952498574791369)
  ·
    refine ⟨33072272431464373931093527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44096363241952498574791369 33072272431464373931093527)
    ·
      refine ⟨49608408647196560896640291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33072272431464373931093527 49608408647196560896640291)
      ·
        refine ⟨74412612970794841344960437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49608408647196560896640291 74412612970794841344960437)
        ·
          refine ⟨6976182466012016376090041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74412612970794841344960437 6976182466012016376090041)
          ·
            refine ⟨5232136849509012282067531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6976182466012016376090041 5232136849509012282067531)
            ·
              refine ⟨7848205274263518423101297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5232136849509012282067531 7848205274263518423101297)
              ·
                refine ⟨5886153955697638817325973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7848205274263518423101297 5886153955697638817325973)
                ·
                  refine ⟨275913466673326819562155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5886153955697638817325973 275913466673326819562155)
                  ·
                    rfl

theorem cell22_2418028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 6].length) (baseStart_2418028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418028 prefixEnd_2418028 := by exact prefixLift 2418028
  have htrace : WordTrace (prefixWord ++ tailWord_2418028) baseStart_2418028 baseEnd_2418028 := by
    simpa [prefixWord, tailWord_2418028, baseEnd_2418028] using wordTrace_append hprefix tailTrace_2418028
  have hstable : (prefixWord ++ tailWord_2418028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418028).length < 2 ^ (prefixWord ++ tailWord_2418028).sum := by decide
  have hdescent : baseEnd_2418028 < baseStart_2418028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418043 : List Nat := [1, 1, 1, 1, 1, 6, 2, 2, 4, 3]
def baseStart_2418043 : Nat := 118140960795 + 2418043 * 2 ^ 59
def prefixEnd_2418043 : Nat := 4983230072969 + 3 ^ 40 * 2418043 * 2
def baseEnd_2418043 : Nat := 827745534826525419561419

theorem tailTrace_2418043 : CollatzResearch.WordTrace tailWord_2418043 prefixEnd_2418043 827745534826525419561419 := by
  unfold tailWord_2418043
  simp only [CollatzResearch.WordTrace]
  refine ⟨88193273578850654711378783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58795515719233769807585855 88193273578850654711378783)
  ·
    refine ⟨132289910368275982067068175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88193273578850654711378783 132289910368275982067068175)
    ·
      refine ⟨198434865552413973100602263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132289910368275982067068175 198434865552413973100602263)
      ·
        refine ⟨297652298328620959650903395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198434865552413973100602263 297652298328620959650903395)
        ·
          refine ⟨446478447492931439476355093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297652298328620959650903395 446478447492931439476355093)
          ·
            refine ⟨20928677226231161225454145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 446478447492931439476355093 20928677226231161225454145)
            ·
              refine ⟨15696507919673370919090609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20928677226231161225454145 15696507919673370919090609)
              ·
                refine ⟨11772380939755028189317957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15696507919673370919090609 11772380939755028189317957)
                ·
                  refine ⟨2207321426204067785497117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11772380939755028189317957 2207321426204067785497117)
                  ·
                    refine ⟨827745534826525419561419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2207321426204067785497117 827745534826525419561419)
                    ·
                      rfl

theorem cell22_2418043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 4, 3].length) (baseStart_2418043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418043 prefixEnd_2418043 := by exact prefixLift 2418043
  have htrace : WordTrace (prefixWord ++ tailWord_2418043) baseStart_2418043 baseEnd_2418043 := by
    simpa [prefixWord, tailWord_2418043, baseEnd_2418043] using wordTrace_append hprefix tailTrace_2418043
  have hstable : (prefixWord ++ tailWord_2418043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418043).length < 2 ^ (prefixWord ++ tailWord_2418043).sum := by decide
  have hdescent : baseEnd_2418043 < baseStart_2418043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418045 : List Nat := [1, 4, 1, 1, 2, 2, 4, 3, 4]
def baseStart_2418045 : Nat := 118140960795 + 2418045 * 2 ^ 59
def prefixEnd_2418045 : Nat := 4983230072969 + 3 ^ 40 * 2418045 * 2
def baseEnd_2418045 : Nat := 275915406489132693670471

theorem tailTrace_2418045 : CollatzResearch.WordTrace tailWord_2418045 prefixEnd_2418045 275915406489132693670471 := by
  unfold tailWord_2418045
  simp only [CollatzResearch.WordTrace]
  refine ⟨88193346524843409052951589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58795564349895606035301059 88193346524843409052951589)
  ·
    refine ⟨16536252473408139197428423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88193346524843409052951589 16536252473408139197428423)
    ·
      refine ⟨24804378710112208796142635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16536252473408139197428423 24804378710112208796142635)
      ·
        refine ⟨37206568065168313194213953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24804378710112208796142635 37206568065168313194213953)
        ·
          refine ⟨27904926048876234895660465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37206568065168313194213953 27904926048876234895660465)
          ·
            refine ⟨20928694536657176171745349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27904926048876234895660465 20928694536657176171745349)
            ·
              refine ⟨3924130225623220532202253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20928694536657176171745349 3924130225623220532202253)
              ·
                refine ⟨1471548834608707699575845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3924130225623220532202253 1471548834608707699575845)
                ·
                  refine ⟨275915406489132693670471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1471548834608707699575845 275915406489132693670471)
                  ·
                    rfl

theorem cell22_2418045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 3, 4].length) (baseStart_2418045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418045 prefixEnd_2418045 := by exact prefixLift 2418045
  have htrace : WordTrace (prefixWord ++ tailWord_2418045) baseStart_2418045 baseEnd_2418045 := by
    simpa [prefixWord, tailWord_2418045, baseEnd_2418045] using wordTrace_append hprefix tailTrace_2418045
  have hstable : (prefixWord ++ tailWord_2418045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418045).length < 2 ^ (prefixWord ++ tailWord_2418045).sum := by decide
  have hdescent : baseEnd_2418045 < baseStart_2418045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418122 : List Nat := [3, 1, 2, 1, 2, 5, 1, 1, 3, 3]
def baseStart_2418122 : Nat := 118140960795 + 2418122 * 2 ^ 59
def prefixEnd_2418122 : Nat := 4983230072969 + 3 ^ 40 * 2418122 * 2
def baseEnd_2418122 : Nat := 827772578140995546836177

theorem tailTrace_2418122 : CollatzResearch.WordTrace tailWord_2418122 prefixEnd_2418122 827772578140995546836177 := by
  unfold tailWord_2418122
  simp only [CollatzResearch.WordTrace]
  refine ⟨22049038736391112800876155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58797436630376300802336413 22049038736391112800876155)
  ·
    refine ⟨33073558104586669201314233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22049038736391112800876155 33073558104586669201314233)
    ·
      refine ⟨24805168578440001900985675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33073558104586669201314233 24805168578440001900985675)
      ·
        refine ⟨37207752867660002851478513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24805168578440001900985675 37207752867660002851478513)
        ·
          refine ⟨27905814650745002138608885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37207752867660002851478513 27905814650745002138608885)
          ·
            refine ⟨2616170123507343950494583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27905814650745002138608885 2616170123507343950494583)
            ·
              refine ⟨3924255185261015925741875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2616170123507343950494583 3924255185261015925741875)
              ·
                refine ⟨5886382777891523888612813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3924255185261015925741875 5886382777891523888612813)
                ·
                  refine ⟨2207393541709321458229805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5886382777891523888612813 2207393541709321458229805)
                  ·
                    refine ⟨827772578140995546836177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2207393541709321458229805 827772578140995546836177)
                    ·
                      rfl

theorem cell22_2418122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 3, 3].length) (baseStart_2418122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418122 prefixEnd_2418122 := by exact prefixLift 2418122
  have htrace : WordTrace (prefixWord ++ tailWord_2418122) baseStart_2418122 baseEnd_2418122 := by
    simpa [prefixWord, tailWord_2418122, baseEnd_2418122] using wordTrace_append hprefix tailTrace_2418122
  have hstable : (prefixWord ++ tailWord_2418122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418122).length < 2 ^ (prefixWord ++ tailWord_2418122).sum := by decide
  have hdescent : baseEnd_2418122 < baseStart_2418122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418133 : List Nat := [1, 3, 2, 3, 1, 1, 2, 1, 1, 7]
def baseStart_2418133 : Nat := 118140960795 + 2418133 * 2 ^ 59
def prefixEnd_2418133 : Nat := 4983230072969 + 3 ^ 40 * 2418133 * 2
def baseEnd_2418133 : Nat := 827776343665795184811143

theorem tailTrace_2418133 : CollatzResearch.WordTrace tailWord_2418133 prefixEnd_2418133 827776343665795184811143 := by
  unfold tailWord_2418133
  simp only [CollatzResearch.WordTrace]
  refine ⟨88196556148524600082155053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58797704099016400054770035 88196556148524600082155053)
  ·
    refine ⟨33073708555696725030808145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88196556148524600082155053 33073708555696725030808145)
    ·
      refine ⟨24805281416772543773106109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33073708555696725030808145 24805281416772543773106109)
      ·
        refine ⟨9301980531289703914914791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24805281416772543773106109 9301980531289703914914791)
        ·
          refine ⟨13952970796934555872372187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9301980531289703914914791 13952970796934555872372187)
          ·
            refine ⟨20929456195401833808558281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13952970796934555872372187 20929456195401833808558281)
            ·
              refine ⟨15697092146551375356418711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20929456195401833808558281 15697092146551375356418711)
              ·
                refine ⟨23545638219827063034628067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15697092146551375356418711 23545638219827063034628067)
                ·
                  refine ⟨35318457329740594551942101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23545638219827063034628067 35318457329740594551942101)
                  ·
                    refine ⟨827776343665795184811143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35318457329740594551942101 827776343665795184811143)
                    ·
                      rfl

theorem cell22_2418133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_2418133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418133 prefixEnd_2418133 := by exact prefixLift 2418133
  have htrace : WordTrace (prefixWord ++ tailWord_2418133) baseStart_2418133 baseEnd_2418133 := by
    simpa [prefixWord, tailWord_2418133, baseEnd_2418133] using wordTrace_append hprefix tailTrace_2418133
  have hstable : (prefixWord ++ tailWord_2418133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418133).length < 2 ^ (prefixWord ++ tailWord_2418133).sum := by decide
  have hdescent : baseEnd_2418133 < baseStart_2418133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418193 : List Nat := [1, 2, 2, 1, 1, 2, 4, 2, 1, 6]
def baseStart_2418193 : Nat := 118140960795 + 2418193 * 2 ^ 59
def prefixEnd_2418193 : Nat := 4983230072969 + 3 ^ 40 * 2418193 * 2
def baseEnd_2418193 : Nat := 827796882891975028310959

theorem tailTrace_2418193 : CollatzResearch.WordTrace tailWord_2418193 prefixEnd_2418193 827796882891975028310959 := by
  unfold tailWord_2418193
  simp only [CollatzResearch.WordTrace]
  refine ⟨88198744528307230329339233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58799163018871486886226155 88198744528307230329339233)
  ·
    refine ⟨66149058396230422747004425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88198744528307230329339233 66149058396230422747004425)
    ·
      refine ⟨49611793797172817060253319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66149058396230422747004425 49611793797172817060253319)
      ·
        refine ⟨74417690695759225590379979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49611793797172817060253319 74417690695759225590379979)
        ·
          refine ⟨111626536043638838385569969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74417690695759225590379979 111626536043638838385569969)
          ·
            refine ⟨83719902032729128789177477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111626536043638838385569969 83719902032729128789177477)
            ·
              refine ⟨15697481631136711647970777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83719902032729128789177477 15697481631136711647970777)
              ·
                refine ⟨11773111223352533735978083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15697481631136711647970777 11773111223352533735978083)
                ·
                  refine ⟨17659666835028800603967125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11773111223352533735978083 17659666835028800603967125)
                  ·
                    refine ⟨827796882891975028310959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17659666835028800603967125 827796882891975028310959)
                    ·
                      rfl

theorem cell22_2418193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_2418193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418193 prefixEnd_2418193 := by exact prefixLift 2418193
  have htrace : WordTrace (prefixWord ++ tailWord_2418193) baseStart_2418193 baseEnd_2418193 := by
    simpa [prefixWord, tailWord_2418193, baseEnd_2418193] using wordTrace_append hprefix tailTrace_2418193
  have hstable : (prefixWord ++ tailWord_2418193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418193).length < 2 ^ (prefixWord ++ tailWord_2418193).sum := by decide
  have hdescent : baseEnd_2418193 < baseStart_2418193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418195 : List Nat := [1, 1, 1, 2, 1, 7, 2, 1, 1, 5]
def baseStart_2418195 : Nat := 118140960795 + 2418195 * 2 ^ 59
def prefixEnd_2418195 : Nat := 4983230072969 + 3 ^ 40 * 2418195 * 2
def baseEnd_2418195 : Nat := 827797567532847689760953

theorem tailTrace_2418195 : CollatzResearch.WordTrace tailWord_2418195 prefixEnd_2418195 827797567532847689760953 := by
  unfold tailWord_2418195
  simp only [CollatzResearch.WordTrace]
  refine ⟨88198817474299984670912039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58799211649533323113941359 88198817474299984670912039)
  ·
    refine ⟨132298226211449977006368059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88198817474299984670912039 132298226211449977006368059)
    ·
      refine ⟨198447339317174965509552089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132298226211449977006368059 198447339317174965509552089)
      ·
        refine ⟨148835504487881224132164067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198447339317174965509552089 148835504487881224132164067)
        ·
          refine ⟨223253256731821836198246101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148835504487881224132164067 223253256731821836198246101)
          ·
            refine ⟨5232498204652074285896393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 223253256731821836198246101 5232498204652074285896393)
            ·
              refine ⟨3924373653489055714422295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5232498204652074285896393 3924373653489055714422295)
              ·
                refine ⟨5886560480233583571633443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3924373653489055714422295 5886560480233583571633443)
                ·
                  refine ⟨8829840720350375357450165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5886560480233583571633443 8829840720350375357450165)
                  ·
                    refine ⟨827797567532847689760953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8829840720350375357450165 827797567532847689760953)
                    ·
                      rfl

theorem cell22_2418195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 5].length) (baseStart_2418195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418195 prefixEnd_2418195 := by exact prefixLift 2418195
  have htrace : WordTrace (prefixWord ++ tailWord_2418195) baseStart_2418195 baseEnd_2418195 := by
    simpa [prefixWord, tailWord_2418195, baseEnd_2418195] using wordTrace_append hprefix tailTrace_2418195
  have hstable : (prefixWord ++ tailWord_2418195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418195).length < 2 ^ (prefixWord ++ tailWord_2418195).sum := by decide
  have hdescent : baseEnd_2418195 < baseStart_2418195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418216 : List Nat := [2, 1, 5, 2, 2, 2, 2, 1, 1, 4]
def baseStart_2418216 : Nat := 118140960795 + 2418216 * 2 ^ 59
def prefixEnd_2418216 : Nat := 4983230072969 + 3 ^ 40 * 2418216 * 2
def baseEnd_2418216 : Nat := 827804756262010634985889

theorem tailTrace_2418216 : CollatzResearch.WordTrace tailWord_2418216 prefixEnd_2418216 827804756262010634985889 := by
  unfold tailWord_2418216
  simp only [CollatzResearch.WordTrace]
  refine ⟨44099791703611952628713251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58799722271482603504951001 44099791703611952628713251)
  ·
    refine ⟨66149687555417928943069877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44099791703611952628713251 66149687555417928943069877)
    ·
      refine ⟨6201533208320430838412801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66149687555417928943069877 6201533208320430838412801)
      ·
        refine ⟨4651149906240323128809601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6201533208320430838412801 4651149906240323128809601)
        ·
          refine ⟨3488362429680242346607201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4651149906240323128809601 3488362429680242346607201)
          ·
            refine ⟨2616271822260181759955401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3488362429680242346607201 2616271822260181759955401)
            ·
              refine ⟨1962203866695136319966551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2616271822260181759955401 1962203866695136319966551)
              ·
                refine ⟨2943305800042704479949827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1962203866695136319966551 2943305800042704479949827)
                ·
                  refine ⟨4414958700064056719924741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2943305800042704479949827 4414958700064056719924741)
                  ·
                    refine ⟨827804756262010634985889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4414958700064056719924741 827804756262010634985889)
                    ·
                      rfl

theorem cell22_2418216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_2418216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418216 prefixEnd_2418216 := by exact prefixLift 2418216
  have htrace : WordTrace (prefixWord ++ tailWord_2418216) baseStart_2418216 baseEnd_2418216 := by
    simpa [prefixWord, tailWord_2418216, baseEnd_2418216] using wordTrace_append hprefix tailTrace_2418216
  have hstable : (prefixWord ++ tailWord_2418216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418216).length < 2 ^ (prefixWord ++ tailWord_2418216).sum := by decide
  have hdescent : baseEnd_2418216 < baseStart_2418216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418229 : List Nat := [1, 3, 3, 1, 1, 5, 1, 2, 2, 3]
def baseStart_2418229 : Nat := 118140960795 + 2418229 * 2 ^ 59
def prefixEnd_2418229 : Nat := 4983230072969 + 3 ^ 40 * 2418229 * 2
def baseEnd_2418229 : Nat := 827809206427682934410849

theorem tailTrace_2418229 : CollatzResearch.WordTrace tailWord_2418229 prefixEnd_2418229 827809206427682934410849 := by
  unfold tailWord_2418229
  simp only [CollatzResearch.WordTrace]
  refine ⟨88200057556176808477649741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58800038370784538985099827 88200057556176808477649741)
  ·
    refine ⟨33075021583566303179118653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88200057556176808477649741 33075021583566303179118653)
    ·
      refine ⟨12403133093837363692169495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33075021583566303179118653 12403133093837363692169495)
      ·
        refine ⟨18604699640756045538254243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12403133093837363692169495 18604699640756045538254243)
        ·
          refine ⟨27907049461134068307381365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18604699640756045538254243 27907049461134068307381365)
          ·
            refine ⟨2616285886981318903817003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27907049461134068307381365 2616285886981318903817003)
            ·
              refine ⟨3924428830471978355725505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2616285886981318903817003 3924428830471978355725505)
              ·
                refine ⟨2943321622853983766794129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3924428830471978355725505 2943321622853983766794129)
                ·
                  refine ⟨2207491217140487825095597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2943321622853983766794129 2207491217140487825095597)
                  ·
                    refine ⟨827809206427682934410849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2207491217140487825095597 827809206427682934410849)
                    ·
                      rfl

theorem cell22_2418229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_2418229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418229 prefixEnd_2418229 := by exact prefixLift 2418229
  have htrace : WordTrace (prefixWord ++ tailWord_2418229) baseStart_2418229 baseEnd_2418229 := by
    simpa [prefixWord, tailWord_2418229, baseEnd_2418229] using wordTrace_append hprefix tailTrace_2418229
  have hstable : (prefixWord ++ tailWord_2418229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418229).length < 2 ^ (prefixWord ++ tailWord_2418229).sum := by decide
  have hdescent : baseEnd_2418229 < baseStart_2418229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418246 : List Nat := [6, 1, 1, 1, 3, 2, 1, 1, 1, 5]
def baseStart_2418246 : Nat := 118140960795 + 2418246 * 2 ^ 59
def prefixEnd_2418246 : Nat := 4983230072969 + 3 ^ 40 * 2418246 * 2
def baseEnd_2418246 : Nat := 827815025875100556735797

theorem tailTrace_2418246 : CollatzResearch.WordTrace tailWord_2418246 prefixEnd_2418246 827815025875100556735797 := by
  unfold tailWord_2418246
  simp only [CollatzResearch.WordTrace]
  refine ⟨2756271174909850636906831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 58800451731410146920679061 2756271174909850636906831)
  ·
    refine ⟨4134406762364775955360247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2756271174909850636906831 4134406762364775955360247)
    ·
      refine ⟨6201610143547163933040371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4134406762364775955360247 6201610143547163933040371)
      ·
        refine ⟨9302415215320745899560557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6201610143547163933040371 9302415215320745899560557)
        ·
          refine ⟨3488405705745279712335209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9302415215320745899560557 3488405705745279712335209)
          ·
            refine ⟨2616304279308959784251407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3488405705745279712335209 2616304279308959784251407)
            ·
              refine ⟨3924456418963439676377111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2616304279308959784251407 3924456418963439676377111)
              ·
                refine ⟨5886684628445159514565667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3924456418963439676377111 5886684628445159514565667)
                ·
                  refine ⟨8830026942667739271848501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5886684628445159514565667 8830026942667739271848501)
                  ·
                    refine ⟨827815025875100556735797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8830026942667739271848501 827815025875100556735797)
                    ·
                      rfl

theorem cell22_2418246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_2418246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418246 prefixEnd_2418246 := by exact prefixLift 2418246
  have htrace : WordTrace (prefixWord ++ tailWord_2418246) baseStart_2418246 baseEnd_2418246 := by
    simpa [prefixWord, tailWord_2418246, baseEnd_2418246] using wordTrace_append hprefix tailTrace_2418246
  have hstable : (prefixWord ++ tailWord_2418246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418246).length < 2 ^ (prefixWord ++ tailWord_2418246).sum := by decide
  have hdescent : baseEnd_2418246 < baseStart_2418246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418283 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 1, 10]
def baseStart_2418283 : Nat := 118140960795 + 2418283 * 2 ^ 59
def prefixEnd_2418283 : Nat := 4983230072969 + 3 ^ 40 * 2418283 * 2
def baseEnd_2418283 : Nat := 827827691731244793560683

theorem tailTrace_2418283 : CollatzResearch.WordTrace tailWord_2418283 prefixEnd_2418283 827827691731244793560683 := by
  unfold tailWord_2418283
  simp only [CollatzResearch.WordTrace]
  refine ⟨88202027097981175700115503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58801351398654117133410335 88202027097981175700115503)
  ·
    refine ⟨132303040646971763550173255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88202027097981175700115503 132303040646971763550173255)
    ·
      refine ⟨198454560970457645325259883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132303040646971763550173255 198454560970457645325259883)
      ·
        refine ⟨297681841455686467987889825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198454560970457645325259883 297681841455686467987889825)
        ·
          refine ⟨223261381091764850990917369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 297681841455686467987889825 223261381091764850990917369)
          ·
            refine ⟨167446035818823638243188027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 223261381091764850990917369 167446035818823638243188027)
            ·
              refine ⟨251169053728235457364782041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167446035818823638243188027 251169053728235457364782041)
              ·
                refine ⟨188376790296176593023586531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 251169053728235457364782041 188376790296176593023586531)
                ·
                  refine ⟨282565185444264889535379797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 188376790296176593023586531 282565185444264889535379797)
                  ·
                    refine ⟨827827691731244793560683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 282565185444264889535379797 827827691731244793560683)
                    ·
                      rfl

theorem cell22_2418283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 10].length) (baseStart_2418283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418283 prefixEnd_2418283 := by exact prefixLift 2418283
  have htrace : WordTrace (prefixWord ++ tailWord_2418283) baseStart_2418283 baseEnd_2418283 := by
    simpa [prefixWord, tailWord_2418283, baseEnd_2418283] using wordTrace_append hprefix tailTrace_2418283
  have hstable : (prefixWord ++ tailWord_2418283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418283).length < 2 ^ (prefixWord ++ tailWord_2418283).sum := by decide
  have hdescent : baseEnd_2418283 < baseStart_2418283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418300 : List Nat := [2, 2, 2, 1, 1, 2, 1, 4, 3, 4]
def baseStart_2418300 : Nat := 118140960795 + 2418300 * 2 ^ 59
def prefixEnd_2418300 : Nat := 4983230072969 + 3 ^ 40 * 2418300 * 2
def baseEnd_2418300 : Nat := 827833511178662415885631

theorem tailTrace_2418300 : CollatzResearch.WordTrace tailWord_2418300 prefixEnd_2418300 827833511178662415885631 := by
  unfold tailWord_2418300
  simp only [CollatzResearch.WordTrace]
  refine ⟨44101323569459793801742177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58801764759279725068989569 44101323569459793801742177)
  ·
    refine ⟨33075992677094845351306633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44101323569459793801742177 33075992677094845351306633)
    ·
      refine ⟨24806994507821134013479975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33075992677094845351306633 24806994507821134013479975)
      ·
        refine ⟨37210491761731701020219963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24806994507821134013479975 37210491761731701020219963)
        ·
          refine ⟨55815737642597551530329945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37210491761731701020219963 55815737642597551530329945)
          ·
            refine ⟨41861803231948163647747459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55815737642597551530329945 41861803231948163647747459)
            ·
              refine ⟨62792704847922245471621189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41861803231948163647747459 62792704847922245471621189)
              ·
                refine ⟨11773632158985421025928973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62792704847922245471621189 11773632158985421025928973)
                ·
                  refine ⟨4415112059619532884723365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11773632158985421025928973 4415112059619532884723365)
                  ·
                    refine ⟨827833511178662415885631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4415112059619532884723365 827833511178662415885631)
                    ·
                      rfl

theorem cell22_2418300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_2418300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418300 prefixEnd_2418300 := by exact prefixLift 2418300
  have htrace : WordTrace (prefixWord ++ tailWord_2418300) baseStart_2418300 baseEnd_2418300 := by
    simpa [prefixWord, tailWord_2418300, baseEnd_2418300] using wordTrace_append hprefix tailTrace_2418300
  have hstable : (prefixWord ++ tailWord_2418300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418300).length < 2 ^ (prefixWord ++ tailWord_2418300).sum := by decide
  have hdescent : baseEnd_2418300 < baseStart_2418300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418349 : List Nat := [1, 5, 2, 1, 1, 1, 3, 4, 4]
def baseStart_2418349 : Nat := 118140960795 + 2418349 * 2 ^ 59
def prefixEnd_2418349 : Nat := 4983230072969 + 3 ^ 40 * 2418349 * 2
def baseEnd_2418349 : Nat := 275950094960014207136827

theorem tailTrace_2418349 : CollatzResearch.WordTrace tailWord_2418349 prefixEnd_2418349 275950094960014207136827 := by
  unfold tailWord_2418349
  simp only [CollatzResearch.WordTrace]
  refine ⟨88204434315742068972018101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58802956210494712648012067 88204434315742068972018101)
  ·
    refine ⟨8269165717100818966126697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88204434315742068972018101 8269165717100818966126697)
    ·
      refine ⟨6201874287825614224595023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8269165717100818966126697 6201874287825614224595023)
      ·
        refine ⟨9302811431738421336892535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6201874287825614224595023 9302811431738421336892535)
        ·
          refine ⟨13954217147607632005338803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9302811431738421336892535 13954217147607632005338803)
          ·
            refine ⟨20931325721411448008008205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13954217147607632005338803 20931325721411448008008205)
            ·
              refine ⟨7849247145529293003003077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20931325721411448008008205 7849247145529293003003077)
              ·
                refine ⟨1471733839786742438063077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7849247145529293003003077 1471733839786742438063077)
                ·
                  refine ⟨275950094960014207136827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1471733839786742438063077 275950094960014207136827)
                  ·
                    rfl

theorem cell22_2418349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_2418349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418349 prefixEnd_2418349 := by exact prefixLift 2418349
  have htrace : WordTrace (prefixWord ++ tailWord_2418349) baseStart_2418349 baseEnd_2418349 := by
    simpa [prefixWord, tailWord_2418349, baseEnd_2418349] using wordTrace_append hprefix tailTrace_2418349
  have hstable : (prefixWord ++ tailWord_2418349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418349).length < 2 ^ (prefixWord ++ tailWord_2418349).sum := by decide
  have hdescent : baseEnd_2418349 < baseStart_2418349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418364 : List Nat := [2, 2, 2, 3, 1, 2, 2, 3, 2, 3]
def baseStart_2418364 : Nat := 118140960795 + 2418364 * 2 ^ 59
def prefixEnd_2418364 : Nat := 4983230072969 + 3 ^ 40 * 2418364 * 2
def baseEnd_2418364 : Nat := 827855419686587582285435

theorem tailTrace_2418364 : CollatzResearch.WordTrace tailWord_2418364 prefixEnd_2418364 827855419686587582285435 := by
  unfold tailWord_2418364
  simp only [CollatzResearch.WordTrace]
  refine ⟨44102490705343863266907073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58803320940458484355876097 44102490705343863266907073)
  ·
    refine ⟨33076868029007897450180305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44102490705343863266907073 33076868029007897450180305)
    ·
      refine ⟨24807651021755923087635229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33076868029007897450180305 24807651021755923087635229)
      ·
        refine ⟨9302869133158471157863211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24807651021755923087635229 9302869133158471157863211)
        ·
          refine ⟨13954303699737706736794817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9302869133158471157863211 13954303699737706736794817)
          ·
            refine ⟨10465727774803280052596113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13954303699737706736794817 10465727774803280052596113)
            ·
              refine ⟨7849295831102460039447085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10465727774803280052596113 7849295831102460039447085)
              ·
                refine ⟨2943485936663422514792657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7849295831102460039447085 2943485936663422514792657)
                ·
                  refine ⟨2207614452497566886094493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2943485936663422514792657 2207614452497566886094493)
                  ·
                    refine ⟨827855419686587582285435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2207614452497566886094493 827855419686587582285435)
                    ·
                      rfl

theorem cell22_2418364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3, 2, 3].length) (baseStart_2418364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418364 prefixEnd_2418364 := by exact prefixLift 2418364
  have htrace : WordTrace (prefixWord ++ tailWord_2418364) baseStart_2418364 baseEnd_2418364 := by
    simpa [prefixWord, tailWord_2418364, baseEnd_2418364] using wordTrace_append hprefix tailTrace_2418364
  have hstable : (prefixWord ++ tailWord_2418364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418364).length < 2 ^ (prefixWord ++ tailWord_2418364).sum := by decide
  have hdescent : baseEnd_2418364 < baseStart_2418364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418392 : List Nat := [2, 1, 2, 2, 3, 1, 1, 2, 5, 3]
def baseStart_2418392 : Nat := 118140960795 + 2418392 * 2 ^ 59
def prefixEnd_2418392 : Nat := 4983230072969 + 3 ^ 40 * 2418392 * 2
def baseEnd_2418392 : Nat := 827865004658804842585349

theorem tailTrace_2418392 : CollatzResearch.WordTrace tailWord_2418392 prefixEnd_2418392 827865004658804842585349 := by
  unfold tailWord_2418392
  simp only [CollatzResearch.WordTrace]
  refine ⟨44103001327293143657916715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58804001769724191543888953 44103001327293143657916715)
  ·
    refine ⟨66154501990939715486875073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44103001327293143657916715 66154501990939715486875073)
    ·
      refine ⟨49615876493204786615156305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66154501990939715486875073 49615876493204786615156305)
      ·
        refine ⟨37211907369903589961367229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49615876493204786615156305 37211907369903589961367229)
        ·
          refine ⟨13954465263713846235512711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37211907369903589961367229 13954465263713846235512711)
          ·
            refine ⟨20931697895570769353269067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13954465263713846235512711 20931697895570769353269067)
            ·
              refine ⟨31397546843356154029903601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20931697895570769353269067 31397546843356154029903601)
              ·
                refine ⟨23548160132517115522427701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31397546843356154029903601 23548160132517115522427701)
                ·
                  refine ⟨2207640012423479580227597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23548160132517115522427701 2207640012423479580227597)
                  ·
                    refine ⟨827865004658804842585349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2207640012423479580227597 827865004658804842585349)
                    ·
                      rfl

theorem cell22_2418392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 5, 3].length) (baseStart_2418392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418392 prefixEnd_2418392 := by exact prefixLift 2418392
  have htrace : WordTrace (prefixWord ++ tailWord_2418392) baseStart_2418392 baseEnd_2418392 := by
    simpa [prefixWord, tailWord_2418392, baseEnd_2418392] using wordTrace_append hprefix tailTrace_2418392
  have hstable : (prefixWord ++ tailWord_2418392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418392).length < 2 ^ (prefixWord ++ tailWord_2418392).sum := by decide
  have hdescent : baseEnd_2418392 < baseStart_2418392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418445 : List Nat := [1, 7, 2, 1, 2, 1, 8]
def baseStart_2418445 : Nat := 118140960795 + 2418445 * 2 ^ 59
def prefixEnd_2418445 : Nat := 4983230072969 + 3 ^ 40 * 2418445 * 2
def baseEnd_2418445 : Nat := 30662338801552976704081

theorem tailTrace_2418445 : CollatzResearch.WordTrace tailWord_2418445 prefixEnd_2418445 30662338801552976704081 := by
  unfold tailWord_2418445
  simp only [CollatzResearch.WordTrace]
  refine ⟨88207935723394277367512789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58805290482262851578341859 88207935723394277367512789)
  ·
    refine ⟨2067373493517053375801081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 88207935723394277367512789 2067373493517053375801081)
    ·
      refine ⟨1550530120137790031850811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2067373493517053375801081 1550530120137790031850811)
      ·
        refine ⟨2325795180206685047776217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1550530120137790031850811 2325795180206685047776217)
        ·
          refine ⟨1744346385155013785832163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2325795180206685047776217 1744346385155013785832163)
          ·
            refine ⟨2616519577732520678748245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1744346385155013785832163 2616519577732520678748245)
            ·
              refine ⟨30662338801552976704081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2616519577732520678748245 30662338801552976704081)
              ·
                rfl

theorem cell22_2418445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 8].length) (baseStart_2418445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418445 prefixEnd_2418445 := by exact prefixLift 2418445
  have htrace : WordTrace (prefixWord ++ tailWord_2418445) baseStart_2418445 baseEnd_2418445 := by
    simpa [prefixWord, tailWord_2418445, baseEnd_2418445] using wordTrace_append hprefix tailTrace_2418445
  have hstable : (prefixWord ++ tailWord_2418445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418445).length < 2 ^ (prefixWord ++ tailWord_2418445).sum := by decide
  have hdescent : baseEnd_2418445 < baseStart_2418445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418467 : List Nat := [1, 1, 1, 4, 2, 1, 5, 1, 6]
def baseStart_2418467 : Nat := 118140960795 + 2418467 * 2 ^ 59
def prefixEnd_2418467 : Nat := 4983230072969 + 3 ^ 40 * 2418467 * 2
def baseEnd_2418467 : Nat := 275963559563843215653373

theorem tailTrace_2418467 : CollatzResearch.WordTrace tailWord_2418467 prefixEnd_2418467 275963559563843215653373 := by
  unfold tailWord_2418467
  simp only [CollatzResearch.WordTrace]
  refine ⟨88208738129314575124813655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58805825419543050083209103 88208738129314575124813655)
  ·
    refine ⟨132313107193971862687220483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88208738129314575124813655 132313107193971862687220483)
    ·
      refine ⟨198469660790957794030830725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132313107193971862687220483 198469660790957794030830725)
      ·
        refine ⟨37213061398304586380780761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 198469660790957794030830725 37213061398304586380780761)
        ·
          refine ⟨27909796048728439785585571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37213061398304586380780761 27909796048728439785585571)
          ·
            refine ⟨41864694073092659678378357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27909796048728439785585571 41864694073092659678378357)
            ·
              refine ⟨3924815069352436844847971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41864694073092659678378357 3924815069352436844847971)
              ·
                refine ⟨5887222604028655267271957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3924815069352436844847971 5887222604028655267271957)
                ·
                  refine ⟨275963559563843215653373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5887222604028655267271957 275963559563843215653373)
                  ·
                    rfl

theorem cell22_2418467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 6].length) (baseStart_2418467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418467 prefixEnd_2418467 := by exact prefixLift 2418467
  have htrace : WordTrace (prefixWord ++ tailWord_2418467) baseStart_2418467 baseEnd_2418467 := by
    simpa [prefixWord, tailWord_2418467, baseEnd_2418467] using wordTrace_append hprefix tailTrace_2418467
  have hstable : (prefixWord ++ tailWord_2418467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418467).length < 2 ^ (prefixWord ++ tailWord_2418467).sum := by decide
  have hdescent : baseEnd_2418467 < baseStart_2418467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418486 : List Nat := [5, 1, 2, 2, 1, 2, 1, 1, 3, 4]
def baseStart_2418486 : Nat := 118140960795 + 2418486 * 2 ^ 59
def prefixEnd_2418486 : Nat := 4983230072969 + 3 ^ 40 * 2418486 * 2
def baseEnd_2418486 : Nat := 827897182779819930735061

theorem tailTrace_2418486 : CollatzResearch.WordTrace tailWord_2418486 prefixEnd_2418486 827897182779819930735061 := by
  unfold tailWord_2418486
  simp only [CollatzResearch.WordTrace]
  refine ⟨5513089444765358835609707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58806287410830494246503541 5513089444765358835609707)
  ·
    refine ⟨8269634167148038253414561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5513089444765358835609707 8269634167148038253414561)
    ·
      refine ⟨6202225625361028690060921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8269634167148038253414561 6202225625361028690060921)
      ·
        refine ⟨4651669219020771517545691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6202225625361028690060921 4651669219020771517545691)
        ·
          refine ⟨6977503828531157276318537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4651669219020771517545691 6977503828531157276318537)
          ·
            refine ⟨5233127871398367957238903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6977503828531157276318537 5233127871398367957238903)
            ·
              refine ⟨7849691807097551935858355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5233127871398367957238903 7849691807097551935858355)
              ·
                refine ⟨11774537710646327903787533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7849691807097551935858355 11774537710646327903787533)
                ·
                  refine ⟨4415451641492372963920325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11774537710646327903787533 4415451641492372963920325)
                  ·
                    refine ⟨827897182779819930735061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4415451641492372963920325 827897182779819930735061)
                    ·
                      rfl

theorem cell22_2418486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_2418486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418486 prefixEnd_2418486 := by exact prefixLift 2418486
  have htrace : WordTrace (prefixWord ++ tailWord_2418486) baseStart_2418486 baseEnd_2418486 := by
    simpa [prefixWord, tailWord_2418486, baseEnd_2418486] using wordTrace_append hprefix tailTrace_2418486
  have hstable : (prefixWord ++ tailWord_2418486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418486).length < 2 ^ (prefixWord ++ tailWord_2418486).sum := by decide
  have hdescent : baseEnd_2418486 < baseStart_2418486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418514 : List Nat := [3, 2, 2, 1, 1, 3, 2, 2, 2, 4]
def baseStart_2418514 : Nat := 118140960795 + 2418514 * 2 ^ 59
def prefixEnd_2418514 : Nat := 4983230072969 + 3 ^ 40 * 2418514 * 2
def baseEnd_2418514 : Nat := 827906767752037191034975

theorem tailTrace_2418514 : CollatzResearch.WordTrace tailWord_2418514 prefixEnd_2418514 827906767752037191034975 := by
  unfold tailWord_2418514
  simp only [CollatzResearch.WordTrace]
  refine ⟨22052613090036075537943649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58806968240096201434516397 22052613090036075537943649)
  ·
    refine ⟨16539459817527056653457737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22052613090036075537943649 16539459817527056653457737)
    ·
      refine ⟨12404594863145292490093303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16539459817527056653457737 12404594863145292490093303)
      ·
        refine ⟨18606892294717938735139955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12404594863145292490093303 18606892294717938735139955)
        ·
          refine ⟨27910338442076908102709933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18606892294717938735139955 27910338442076908102709933)
          ·
            refine ⟨10466376915778840538516225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27910338442076908102709933 10466376915778840538516225)
            ·
              refine ⟨7849782686834130403887169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10466376915778840538516225 7849782686834130403887169)
              ·
                refine ⟨5887337015125597802915377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7849782686834130403887169 5887337015125597802915377)
                ·
                  refine ⟨4415502761344198352186533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5887337015125597802915377 4415502761344198352186533)
                  ·
                    refine ⟨827906767752037191034975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4415502761344198352186533 827906767752037191034975)
                    ·
                      rfl

theorem cell22_2418514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_2418514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418514 prefixEnd_2418514 := by exact prefixLift 2418514
  have htrace : WordTrace (prefixWord ++ tailWord_2418514) baseStart_2418514 baseEnd_2418514 := by
    simpa [prefixWord, tailWord_2418514, baseEnd_2418514] using wordTrace_append hprefix tailTrace_2418514
  have hstable : (prefixWord ++ tailWord_2418514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418514).length < 2 ^ (prefixWord ++ tailWord_2418514).sum := by decide
  have hdescent : baseEnd_2418514 < baseStart_2418514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418516 : List Nat := [2, 4, 1, 1, 3, 1, 1, 4, 2, 3]
def baseStart_2418516 : Nat := 118140960795 + 2418516 * 2 ^ 59
def prefixEnd_2418516 : Nat := 4983230072969 + 3 ^ 40 * 2418516 * 2
def baseEnd_2418516 : Nat := 827907452392909852484969

theorem tailTrace_2418516 : CollatzResearch.WordTrace tailWord_2418516 prefixEnd_2418516 827907452392909852484969 := by
  unfold tailWord_2418516
  simp only [CollatzResearch.WordTrace]
  refine ⟨44105262653068528246673701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58807016870758037662231601 44105262653068528246673701)
  ·
    refine ⟨8269736747450349046251319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44105262653068528246673701 8269736747450349046251319)
    ·
      refine ⟨12404605121175523569376979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8269736747450349046251319 12404605121175523569376979)
      ·
        refine ⟨18606907681763285354065469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12404605121175523569376979 18606907681763285354065469)
        ·
          refine ⟨6977590380661232007774551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18606907681763285354065469 6977590380661232007774551)
          ·
            refine ⟨10466385570991848011661827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6977590380661232007774551 10466385570991848011661827)
            ·
              refine ⟨15699578356487772017492741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10466385570991848011661827 15699578356487772017492741)
              ·
                refine ⟨2943670941841457253279889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15699578356487772017492741 2943670941841457253279889)
                ·
                  refine ⟨2207753206381092939959917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2943670941841457253279889 2207753206381092939959917)
                  ·
                    refine ⟨827907452392909852484969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2207753206381092939959917 827907452392909852484969)
                    ·
                      rfl

theorem cell22_2418516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_2418516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418516 prefixEnd_2418516 := by exact prefixLift 2418516
  have htrace : WordTrace (prefixWord ++ tailWord_2418516) baseStart_2418516 baseEnd_2418516 := by
    simpa [prefixWord, tailWord_2418516, baseEnd_2418516] using wordTrace_append hprefix tailTrace_2418516
  have hstable : (prefixWord ++ tailWord_2418516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418516).length < 2 ^ (prefixWord ++ tailWord_2418516).sum := by decide
  have hdescent : baseEnd_2418516 < baseStart_2418516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418557 : List Nat := [1, 4, 1, 1, 2, 1, 1, 4, 7]
def baseStart_2418557 : Nat := 118140960795 + 2418557 * 2 ^ 59
def prefixEnd_2418557 : Nat := 4983230072969 + 3 ^ 40 * 2418557 * 2
def baseEnd_2418557 : Nat := 275973829176933137403281

theorem tailTrace_2418557 : CollatzResearch.WordTrace tailWord_2418557 prefixEnd_2418557 275973829176933137403281 := by
  unfold tailWord_2418557
  simp only [CollatzResearch.WordTrace]
  refine ⟨88212020698988520495589925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58808013799325680330393283 88212020698988520495589925)
  ·
    refine ⟨16539753881060347592923111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88212020698988520495589925 16539753881060347592923111)
    ·
      refine ⟨24809630821590521389384667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16539753881060347592923111 24809630821590521389384667)
      ·
        refine ⟨37214446232385782084077001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24809630821590521389384667 37214446232385782084077001)
        ·
          refine ⟨27910834674289336563057751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37214446232385782084077001 27910834674289336563057751)
          ·
            refine ⟨41866252011434004844586627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27910834674289336563057751 41866252011434004844586627)
            ·
              refine ⟨62799378017151007266879941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41866252011434004844586627 62799378017151007266879941)
              ·
                refine ⟨11774883378215813862539989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62799378017151007266879941 11774883378215813862539989)
                ·
                  refine ⟨275973829176933137403281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11774883378215813862539989 275973829176933137403281)
                  ·
                    rfl

theorem cell22_2418557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_2418557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418557 prefixEnd_2418557 := by exact prefixLift 2418557
  have htrace : WordTrace (prefixWord ++ tailWord_2418557) baseStart_2418557 baseEnd_2418557 := by
    simpa [prefixWord, tailWord_2418557, baseEnd_2418557] using wordTrace_append hprefix tailTrace_2418557
  have hstable : (prefixWord ++ tailWord_2418557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418557).length < 2 ^ (prefixWord ++ tailWord_2418557).sum := by decide
  have hdescent : baseEnd_2418557 < baseStart_2418557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418578 : List Nat := [3, 2, 3, 2, 1, 2, 2, 1, 3, 3]
def baseStart_2418578 : Nat := 118140960795 + 2418578 * 2 ^ 59
def prefixEnd_2418578 : Nat := 4983230072969 + 3 ^ 40 * 2418578 * 2
def baseEnd_2418578 : Nat := 827928676259962357434779

theorem tailTrace_2418578 : CollatzResearch.WordTrace tailWord_2418578 prefixEnd_2418578 827928676259962357434779 := by
  unfold tailWord_2418578
  simp only [CollatzResearch.WordTrace]
  refine ⟨22053196657978110270526097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58808524421274960721402925 22053196657978110270526097)
  ·
    refine ⟨16539897493483582702894573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22053196657978110270526097 16539897493483582702894573)
    ·
      refine ⟨6202461560056343513585465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16539897493483582702894573 6202461560056343513585465)
      ·
        refine ⟨4651846170042257635189099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6202461560056343513585465 4651846170042257635189099)
        ·
          refine ⟨6977769255063386452783649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4651846170042257635189099 6977769255063386452783649)
          ·
            refine ⟨5233326941297539839587737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6977769255063386452783649 5233326941297539839587737)
            ·
              refine ⟨3924995205973154879690803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5233326941297539839587737 3924995205973154879690803)
              ·
                refine ⟨5887492808959732319536205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3924995205973154879690803 5887492808959732319536205)
                ·
                  refine ⟨2207809803359899619826077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5887492808959732319536205 2207809803359899619826077)
                  ·
                    refine ⟨827928676259962357434779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2207809803359899619826077 827928676259962357434779)
                    ·
                      rfl

theorem cell22_2418578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_2418578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418578 prefixEnd_2418578 := by exact prefixLift 2418578
  have htrace : WordTrace (prefixWord ++ tailWord_2418578) baseStart_2418578 baseEnd_2418578 := by
    simpa [prefixWord, tailWord_2418578, baseEnd_2418578] using wordTrace_append hprefix tailTrace_2418578
  have hstable : (prefixWord ++ tailWord_2418578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418578).length < 2 ^ (prefixWord ++ tailWord_2418578).sum := by decide
  have hdescent : baseEnd_2418578 < baseStart_2418578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418589 : List Nat := [1, 4, 2, 1, 2, 2, 2, 1, 2, 5]
def baseStart_2418589 : Nat := 118140960795 + 2418589 * 2 ^ 59
def prefixEnd_2418589 : Nat := 4983230072969 + 3 ^ 40 * 2418589 * 2
def baseEnd_2418589 : Nat := 827932441784761995409745

theorem tailTrace_2418589 : CollatzResearch.WordTrace tailWord_2418589 prefixEnd_2418589 827932441784761995409745 := by
  unfold tailWord_2418589
  simp only [CollatzResearch.WordTrace]
  refine ⟨88213187834872589960754821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58808791889915059973836547 88213187834872589960754821)
  ·
    refine ⟨16539972719038610617641529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88213187834872589960754821 16539972719038610617641529)
    ·
      refine ⟨12404979539278957963231147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16539972719038610617641529 12404979539278957963231147)
      ·
        refine ⟨18607469308918436944846721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12404979539278957963231147 18607469308918436944846721)
        ·
          refine ⟨13955601981688827708635041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18607469308918436944846721 13955601981688827708635041)
          ·
            refine ⟨10466701486266620781476281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13955601981688827708635041 10466701486266620781476281)
            ·
              refine ⟨7850026114699965586107211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10466701486266620781476281 7850026114699965586107211)
              ·
                refine ⟨11775039172049948379160817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7850026114699965586107211 11775039172049948379160817)
                ·
                  refine ⟨8831279379037461284370613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11775039172049948379160817 8831279379037461284370613)
                  ·
                    refine ⟨827932441784761995409745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8831279379037461284370613 827932441784761995409745)
                    ·
                      rfl

theorem cell22_2418589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_2418589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418589 prefixEnd_2418589 := by exact prefixLift 2418589
  have htrace : WordTrace (prefixWord ++ tailWord_2418589) baseStart_2418589 baseEnd_2418589 := by
    simpa [prefixWord, tailWord_2418589, baseEnd_2418589] using wordTrace_append hprefix tailTrace_2418589
  have hstable : (prefixWord ++ tailWord_2418589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418589).length < 2 ^ (prefixWord ++ tailWord_2418589).sum := by decide
  have hdescent : baseEnd_2418589 < baseStart_2418589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418621 : List Nat := [1, 4, 1, 2, 3, 1, 2, 3, 1, 4]
def baseStart_2418621 : Nat := 118140960795 + 2418621 * 2 ^ 59
def prefixEnd_2418621 : Nat := 4983230072969 + 3 ^ 40 * 2418621 * 2
def baseEnd_2418621 : Nat := 827943396038724578609647

theorem tailTrace_2418621 : CollatzResearch.WordTrace tailWord_2418621 prefixEnd_2418621 827943396038724578609647 := by
  unfold tailWord_2418621
  simp only [CollatzResearch.WordTrace]
  refine ⟨88214354970756659425919717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58809569980504439617279811 88214354970756659425919717)
  ·
    refine ⟨16540191557016873642359947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88214354970756659425919717 16540191557016873642359947)
    ·
      refine ⟨24810287335525310463539921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16540191557016873642359947 24810287335525310463539921)
      ·
        refine ⟨18607715501643982847654941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24810287335525310463539921 18607715501643982847654941)
        ·
          refine ⟨6977893313116493567870603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18607715501643982847654941 6977893313116493567870603)
          ·
            refine ⟨10466839969674740351805905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6977893313116493567870603 10466839969674740351805905)
            ·
              refine ⟨7850129977256055263854429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10466839969674740351805905 7850129977256055263854429)
              ·
                refine ⟨2943798741471020723945411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7850129977256055263854429 2943798741471020723945411)
                ·
                  refine ⟨4415698112206531085918117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2943798741471020723945411 4415698112206531085918117)
                  ·
                    refine ⟨827943396038724578609647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4415698112206531085918117 827943396038724578609647)
                    ·
                      rfl

theorem cell22_2418621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_2418621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418621 prefixEnd_2418621 := by exact prefixLift 2418621
  have htrace : WordTrace (prefixWord ++ tailWord_2418621) baseStart_2418621 baseEnd_2418621 := by
    simpa [prefixWord, tailWord_2418621, baseEnd_2418621] using wordTrace_append hprefix tailTrace_2418621
  have hstable : (prefixWord ++ tailWord_2418621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418621).length < 2 ^ (prefixWord ++ tailWord_2418621).sum := by decide
  have hdescent : baseEnd_2418621 < baseStart_2418621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418636 : List Nat := [2, 2, 1, 4, 1, 4, 1, 1, 6]
def baseStart_2418636 : Nat := 118140960795 + 2418636 * 2 ^ 59
def prefixEnd_2418636 : Nat := 4983230072969 + 3 ^ 40 * 2418636 * 2
def baseEnd_2418636 : Nat := 275982843615089846494867

theorem tailTrace_2418636 : CollatzResearch.WordTrace tailWord_2418636 prefixEnd_2418636 275982843615089846494867 := by
  unfold tailWord_2418636
  simp only [CollatzResearch.WordTrace]
  refine ⟨44107451032851158493857881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58809934710468211325143841 44107451032851158493857881)
  ·
    refine ⟨33080588274638368870393411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44107451032851158493857881 33080588274638368870393411)
    ·
      refine ⟨49620882411957553305590117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33080588274638368870393411 49620882411957553305590117)
      ·
        refine ⟨9303915452242041244798147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49620882411957553305590117 9303915452242041244798147)
        ·
          refine ⟨13955873178363061867197221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9303915452242041244798147 13955873178363061867197221)
          ·
            refine ⟨2616726220943074100099479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13955873178363061867197221 2616726220943074100099479)
            ·
              refine ⟨3925089331414611150149219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2616726220943074100099479 3925089331414611150149219)
              ·
                refine ⟨5887633997121916725223829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3925089331414611150149219 5887633997121916725223829)
                ·
                  refine ⟨275982843615089846494867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5887633997121916725223829 275982843615089846494867)
                  ·
                    rfl

theorem cell22_2418636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 6].length) (baseStart_2418636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418636 prefixEnd_2418636 := by exact prefixLift 2418636
  have htrace : WordTrace (prefixWord ++ tailWord_2418636) baseStart_2418636 baseEnd_2418636 := by
    simpa [prefixWord, tailWord_2418636, baseEnd_2418636] using wordTrace_append hprefix tailTrace_2418636
  have hstable : (prefixWord ++ tailWord_2418636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418636).length < 2 ^ (prefixWord ++ tailWord_2418636).sum := by decide
  have hdescent : baseEnd_2418636 < baseStart_2418636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418666 : List Nat := [3, 1, 3, 1, 2, 1, 4, 1, 2, 4]
def baseStart_2418666 : Nat := 118140960795 + 2418666 * 2 ^ 59
def prefixEnd_2418666 : Nat := 4983230072969 + 3 ^ 40 * 2418666 * 2
def baseEnd_2418666 : Nat := 827958800458359461234509

theorem tailTrace_2418666 : CollatzResearch.WordTrace tailWord_2418666 prefixEnd_2418666 827958800458359461234509 := by
  unfold tailWord_2418666
  simp only [CollatzResearch.WordTrace]
  refine ⟨22053999063898408027826963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58810664170395754740871901 22053999063898408027826963)
  ·
    refine ⟨33080998595847612041740445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22053999063898408027826963 33080998595847612041740445)
    ·
      refine ⟨12405374473442854515652667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33080998595847612041740445 12405374473442854515652667)
      ·
        refine ⟨18608061710164281773479001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12405374473442854515652667 18608061710164281773479001)
        ·
          refine ⟨13956046282623211330109251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18608061710164281773479001 13956046282623211330109251)
          ·
            refine ⟨20934069423934816995163877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13956046282623211330109251 20934069423934816995163877)
            ·
              refine ⟨3925138016987778186593227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20934069423934816995163877 3925138016987778186593227)
              ·
                refine ⟨5887707025481667279889841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3925138016987778186593227 5887707025481667279889841)
                ·
                  refine ⟨4415780269111250459917381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5887707025481667279889841 4415780269111250459917381)
                  ·
                    refine ⟨827958800458359461234509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4415780269111250459917381 827958800458359461234509)
                    ·
                      rfl

theorem cell22_2418666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_2418666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418666 prefixEnd_2418666 := by exact prefixLift 2418666
  have htrace : WordTrace (prefixWord ++ tailWord_2418666) baseStart_2418666 baseEnd_2418666 := by
    simpa [prefixWord, tailWord_2418666, baseEnd_2418666] using wordTrace_append hprefix tailTrace_2418666
  have hstable : (prefixWord ++ tailWord_2418666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418666).length < 2 ^ (prefixWord ++ tailWord_2418666).sum := by decide
  have hdescent : baseEnd_2418666 < baseStart_2418666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418696 : List Nat := [2, 1, 3, 2, 1, 2, 2, 3, 3, 3]
def baseStart_2418696 : Nat := 118140960795 + 2418696 * 2 ^ 59
def prefixEnd_2418696 : Nat := 4983230072969 + 3 ^ 40 * 2418696 * 2
def baseEnd_2418696 : Nat := 827969070071449382984417

theorem tailTrace_2418696 : CollatzResearch.WordTrace tailWord_2418696 prefixEnd_2418696 827969070071449382984417 := by
  unfold tailWord_2418696
  simp only [CollatzResearch.WordTrace]
  refine ⟨44108545222742473617449971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58811393630323298156599961 44108545222742473617449971)
  ·
    refine ⟨66162817834113710426174957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44108545222742473617449971 66162817834113710426174957)
    ·
      refine ⟨24811056687792641409815609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66162817834113710426174957 24811056687792641409815609)
      ·
        refine ⟨18608292515844481057361707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24811056687792641409815609 18608292515844481057361707)
        ·
          refine ⟨27912438773766721586042561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18608292515844481057361707 27912438773766721586042561)
          ·
            refine ⟨20934329080325041189531921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27912438773766721586042561 20934329080325041189531921)
            ·
              refine ⟨15700746810243780892148941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20934329080325041189531921 15700746810243780892148941)
              ·
                refine ⟨5887780053841417834555853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15700746810243780892148941 5887780053841417834555853)
                ·
                  refine ⟨2207917520190531687958445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5887780053841417834555853 2207917520190531687958445)
                  ·
                    refine ⟨827969070071449382984417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2207917520190531687958445 827969070071449382984417)
                    ·
                      rfl

theorem cell22_2418696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 3, 3].length) (baseStart_2418696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418696 prefixEnd_2418696 := by exact prefixLift 2418696
  have htrace : WordTrace (prefixWord ++ tailWord_2418696) baseStart_2418696 baseEnd_2418696 := by
    simpa [prefixWord, tailWord_2418696, baseEnd_2418696] using wordTrace_append hprefix tailTrace_2418696
  have hstable : (prefixWord ++ tailWord_2418696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418696).length < 2 ^ (prefixWord ++ tailWord_2418696).sum := by decide
  have hdescent : baseEnd_2418696 < baseStart_2418696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418698 : List Nat := [3, 1, 2, 2, 5, 1, 1, 7]
def baseStart_2418698 : Nat := 118140960795 + 2418698 * 2 ^ 59
def prefixEnd_2418698 : Nat := 4983230072969 + 3 ^ 40 * 2418698 * 2
def baseEnd_2418698 : Nat := 91996639412480227159379

theorem tailTrace_2418698 : CollatzResearch.WordTrace tailWord_2418698 prefixEnd_2418698 91996639412480227159379 := by
  unfold tailWord_2418698
  simp only [CollatzResearch.WordTrace]
  refine ⟨22054290847869425394118187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58811442260985134384315165 22054290847869425394118187)
  ·
    refine ⟨33081436271804138091177281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22054290847869425394118187 33081436271804138091177281)
    ·
      refine ⟨24811077203853103568382961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33081436271804138091177281 24811077203853103568382961)
      ·
        refine ⟨18608307902889827676287221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24811077203853103568382961 18608307902889827676287221)
        ·
          refine ⟨1744528865895921344651927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18608307902889827676287221 1744528865895921344651927)
          ·
            refine ⟨2616793298843882016977891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1744528865895921344651927 2616793298843882016977891)
            ·
              refine ⟨3925189948265823025466837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2616793298843882016977891 3925189948265823025466837)
              ·
                refine ⟨91996639412480227159379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3925189948265823025466837 91996639412480227159379)
                ·
                  rfl

theorem cell22_2418698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 7].length) (baseStart_2418698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418698 prefixEnd_2418698 := by exact prefixLift 2418698
  have htrace : WordTrace (prefixWord ++ tailWord_2418698) baseStart_2418698 baseEnd_2418698 := by
    simpa [prefixWord, tailWord_2418698, baseEnd_2418698] using wordTrace_append hprefix tailTrace_2418698
  have hstable : (prefixWord ++ tailWord_2418698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418698).length < 2 ^ (prefixWord ++ tailWord_2418698).sum := by decide
  have hdescent : baseEnd_2418698 < baseStart_2418698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418730 : List Nat := [3, 1, 4, 1, 2, 1, 1, 5, 1, 3]
def baseStart_2418730 : Nat := 118140960795 + 2418730 * 2 ^ 59
def prefixEnd_2418730 : Nat := 4983230072969 + 3 ^ 40 * 2418730 * 2
def baseEnd_2418730 : Nat := 827980708966284627634313

theorem tailTrace_2418730 : CollatzResearch.WordTrace tailWord_2418730 prefixEnd_2418730 827980708966284627634313 := by
  unfold tailWord_2418730
  simp only [CollatzResearch.WordTrace]
  refine ⟨22054582631840442760409411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58812220351574514027758429 22054582631840442760409411)
  ·
    refine ⟨33081873947760664140614117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22054582631840442760409411 33081873947760664140614117)
    ·
      refine ⟨6202851365205124526365147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33081873947760664140614117 6202851365205124526365147)
      ·
        refine ⟨9304277047807686789547721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6202851365205124526365147 9304277047807686789547721)
        ·
          refine ⟨6978207785855765092160791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9304277047807686789547721 6978207785855765092160791)
          ·
            refine ⟨10467311678783647638241187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6978207785855765092160791 10467311678783647638241187)
            ·
              refine ⟨15700967518175471457361781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10467311678783647638241187 15700967518175471457361781)
              ·
                refine ⟨1471965704828950449127667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15700967518175471457361781 1471965704828950449127667)
                ·
                  refine ⟨2207948557243425673691501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1471965704828950449127667 2207948557243425673691501)
                  ·
                    refine ⟨827980708966284627634313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2207948557243425673691501 827980708966284627634313)
                    ·
                      rfl

theorem cell22_2418730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_2418730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418730 prefixEnd_2418730 := by exact prefixLift 2418730
  have htrace : WordTrace (prefixWord ++ tailWord_2418730) baseStart_2418730 baseEnd_2418730 := by
    simpa [prefixWord, tailWord_2418730, baseEnd_2418730] using wordTrace_append hprefix tailTrace_2418730
  have hstable : (prefixWord ++ tailWord_2418730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418730).length < 2 ^ (prefixWord ++ tailWord_2418730).sum := by decide
  have hdescent : baseEnd_2418730 < baseStart_2418730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418758 : List Nat := [6, 1, 1, 1, 1, 1, 1, 3, 2, 5]
def baseStart_2418758 : Nat := 118140960795 + 2418758 * 2 ^ 59
def prefixEnd_2418758 : Nat := 4983230072969 + 3 ^ 40 * 2418758 * 2
def baseEnd_2418758 : Nat := 827990293938501887934227

theorem tailTrace_2418758 : CollatzResearch.WordTrace tailWord_2418758 prefixEnd_2418758 827990293938501887934227 := by
  unfold tailWord_2418758
  simp only [CollatzResearch.WordTrace]
  refine ⟨2756854742851885369489279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 58812901180840221215771285 2756854742851885369489279)
  ·
    refine ⟨4135282114277828054233919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2756854742851885369489279 4135282114277828054233919)
    ·
      refine ⟨6202923171416742081350879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4135282114277828054233919 6202923171416742081350879)
      ·
        refine ⟨9304384757125113122026319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6202923171416742081350879 9304384757125113122026319)
        ·
          refine ⟨13956577135687669683039479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9304384757125113122026319 13956577135687669683039479)
          ·
            refine ⟨20934865703531504524559219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13956577135687669683039479 20934865703531504524559219)
            ·
              refine ⟨31402298555297256786838829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20934865703531504524559219 31402298555297256786838829)
              ·
                refine ⟨11775861958236471295064561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31402298555297256786838829 11775861958236471295064561)
                ·
                  refine ⟨8831896468677353471298421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11775861958236471295064561 8831896468677353471298421)
                  ·
                    refine ⟨827990293938501887934227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8831896468677353471298421 827990293938501887934227)
                    ·
                      rfl

theorem cell22_2418758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_2418758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418758 prefixEnd_2418758 := by exact prefixLift 2418758
  have htrace : WordTrace (prefixWord ++ tailWord_2418758) baseStart_2418758 baseEnd_2418758 := by
    simpa [prefixWord, tailWord_2418758, baseEnd_2418758] using wordTrace_append hprefix tailTrace_2418758
  have hstable : (prefixWord ++ tailWord_2418758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418758).length < 2 ^ (prefixWord ++ tailWord_2418758).sum := by decide
  have hdescent : baseEnd_2418758 < baseStart_2418758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418773 : List Nat := [1, 3, 2, 2, 1, 4, 2, 2, 1, 4]
def baseStart_2418773 : Nat := 118140960795 + 2418773 * 2 ^ 59
def prefixEnd_2418773 : Nat := 4983230072969 + 3 ^ 40 * 2418773 * 2
def baseEnd_2418773 : Nat := 827995428745046848809181

theorem tailTrace_2418773 : CollatzResearch.WordTrace tailWord_2418773 prefixEnd_2418773 827995428745046848809181 := by
  unfold tailWord_2418773
  simp only [CollatzResearch.WordTrace]
  refine ⟨88219898866205989385452973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58813265910803992923635315 88219898866205989385452973)
  ·
    refine ⟨33082462074827246019544865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88219898866205989385452973 33082462074827246019544865)
    ·
      refine ⟨24811846556120434514658649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33082462074827246019544865 24811846556120434514658649)
      ·
        refine ⟨18608884917090325885993987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24811846556120434514658649 18608884917090325885993987)
        ·
          refine ⟨27913327375635488828990981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18608884917090325885993987 27913327375635488828990981)
          ·
            refine ⟨5233748882931654155435809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27913327375635488828990981 5233748882931654155435809)
            ·
              refine ⟨3925311662198740616576857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5233748882931654155435809 3925311662198740616576857)
              ·
                refine ⟨2943983746649055462432643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3925311662198740616576857 2943983746649055462432643)
                ·
                  refine ⟨4415975619973583193648965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2943983746649055462432643 4415975619973583193648965)
                  ·
                    refine ⟨827995428745046848809181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4415975619973583193648965 827995428745046848809181)
                    ·
                      rfl

theorem cell22_2418773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_2418773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418773 prefixEnd_2418773 := by exact prefixLift 2418773
  have htrace : WordTrace (prefixWord ++ tailWord_2418773) baseStart_2418773 baseEnd_2418773 := by
    simpa [prefixWord, tailWord_2418773, baseEnd_2418773] using wordTrace_append hprefix tailTrace_2418773
  have hstable : (prefixWord ++ tailWord_2418773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418773).length < 2 ^ (prefixWord ++ tailWord_2418773).sum := by decide
  have hdescent : baseEnd_2418773 < baseStart_2418773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418788 : List Nat := [2, 3, 1, 1, 2, 1, 5, 3, 4]
def baseStart_2418788 : Nat := 118140960795 + 2418788 * 2 ^ 59
def prefixEnd_2418788 : Nat := 4983230072969 + 3 ^ 40 * 2418788 * 2
def baseEnd_2418788 : Nat := 276000187850530603228045

theorem tailTrace_2418788 : CollatzResearch.WordTrace tailWord_2418788 prefixEnd_2418788 276000187850530603228045 := by
  unfold tailWord_2418788
  simp only [CollatzResearch.WordTrace]
  refine ⟨44110222980575823473624509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58813630640767764631499345 44110222980575823473624509)
  ·
    refine ⟨16541333617715933802609191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44110222980575823473624509 16541333617715933802609191)
    ·
      refine ⟨24812000426573900703913787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16541333617715933802609191 24812000426573900703913787)
      ·
        refine ⟨37218000639860851055870681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24812000426573900703913787 37218000639860851055870681)
        ·
          refine ⟨27913500479895638291903011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37218000639860851055870681 27913500479895638291903011)
          ·
            refine ⟨41870250719843457437854517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27913500479895638291903011 41870250719843457437854517)
            ·
              refine ⟨3925336004985324134798861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41870250719843457437854517 3925336004985324134798861)
              ·
                refine ⟨1472001001869496550549573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3925336004985324134798861 1472001001869496550549573)
                ·
                  refine ⟨276000187850530603228045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1472001001869496550549573 276000187850530603228045)
                  ·
                    rfl

theorem cell22_2418788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 3, 4].length) (baseStart_2418788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418788 prefixEnd_2418788 := by exact prefixLift 2418788
  have htrace : WordTrace (prefixWord ++ tailWord_2418788) baseStart_2418788 baseEnd_2418788 := by
    simpa [prefixWord, tailWord_2418788, baseEnd_2418788] using wordTrace_append hprefix tailTrace_2418788
  have hstable : (prefixWord ++ tailWord_2418788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418788).length < 2 ^ (prefixWord ++ tailWord_2418788).sum := by decide
  have hdescent : baseEnd_2418788 < baseStart_2418788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418799 : List Nat := [1, 1, 2, 1, 3, 4, 10]
def baseStart_2418799 : Nat := 118140960795 + 2418799 * 2 ^ 59
def prefixEnd_2418799 : Nat := 4983230072969 + 3 ^ 40 * 2418799 * 2
def baseEnd_2418799 : Nat := 30666827002829312876263

theorem tailTrace_2418799 : CollatzResearch.WordTrace tailWord_2418799 prefixEnd_2418799 30666827002829312876263 := by
  unfold tailWord_2418799
  simp only [CollatzResearch.WordTrace]
  refine ⟨88220847164111795825899451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58813898109407863883932967 88220847164111795825899451)
  ·
    refine ⟨132331270746167693738849177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88220847164111795825899451 132331270746167693738849177)
    ·
      refine ⟨99248453059625770304136883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132331270746167693738849177 99248453059625770304136883)
      ·
        refine ⟨148872679589438655456205325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99248453059625770304136883 148872679589438655456205325)
        ·
          refine ⟨55827254846039495796076997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148872679589438655456205325 55827254846039495796076997)
          ·
            refine ⟨10467610283632405461764437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55827254846039495796076997 10467610283632405461764437)
            ·
              refine ⟨30666827002829312876263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10467610283632405461764437 30666827002829312876263)
              ·
                rfl

theorem cell22_2418799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 10].length) (baseStart_2418799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418799 prefixEnd_2418799 := by exact prefixLift 2418799
  have htrace : WordTrace (prefixWord ++ tailWord_2418799) baseStart_2418799 baseEnd_2418799 := by
    simpa [prefixWord, tailWord_2418799, baseEnd_2418799] using wordTrace_append hprefix tailTrace_2418799
  have hstable : (prefixWord ++ tailWord_2418799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418799).length < 2 ^ (prefixWord ++ tailWord_2418799).sum := by decide
  have hdescent : baseEnd_2418799 < baseStart_2418799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418801 : List Nat := [1, 2, 2, 2, 1, 1, 5, 2, 2, 4]
def baseStart_2418801 : Nat := 118140960795 + 2418801 * 2 ^ 59
def prefixEnd_2418801 : Nat := 4983230072969 + 3 ^ 40 * 2418801 * 2
def baseEnd_2418801 : Nat := 828005013717264109109095

theorem tailTrace_2418801 : CollatzResearch.WordTrace tailWord_2418801 prefixEnd_2418801 828005013717264109109095 := by
  unfold tailWord_2418801
  simp only [CollatzResearch.WordTrace]
  refine ⟨88220920110104550167472257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58813946740069700111648171 88220920110104550167472257)
  ·
    refine ⟨66165690082578412625604193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88220920110104550167472257 66165690082578412625604193)
    ·
      refine ⟨49624267561933809469203145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66165690082578412625604193 49624267561933809469203145)
      ·
        refine ⟨37218200671450357101902359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49624267561933809469203145 37218200671450357101902359)
        ·
          refine ⟨55827301007175535652853539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37218200671450357101902359 55827301007175535652853539)
          ·
            refine ⟨83740951510763303479280309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55827301007175535652853539 83740951510763303479280309)
            ·
              refine ⟨7850714204134059701182529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83740951510763303479280309 7850714204134059701182529)
              ·
                refine ⟨5888035653100544775886897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7850714204134059701182529 5888035653100544775886897)
                ·
                  refine ⟨4416026739825408581915173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5888035653100544775886897 4416026739825408581915173)
                  ·
                    refine ⟨828005013717264109109095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4416026739825408581915173 828005013717264109109095)
                    ·
                      rfl

theorem cell22_2418801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2, 4].length) (baseStart_2418801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418801 prefixEnd_2418801 := by exact prefixLift 2418801
  have htrace : WordTrace (prefixWord ++ tailWord_2418801) baseStart_2418801 baseEnd_2418801 := by
    simpa [prefixWord, tailWord_2418801, baseEnd_2418801] using wordTrace_append hprefix tailTrace_2418801
  have hstable : (prefixWord ++ tailWord_2418801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418801).length < 2 ^ (prefixWord ++ tailWord_2418801).sum := by decide
  have hdescent : baseEnd_2418801 < baseStart_2418801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418882 : List Nat := [3, 5, 1, 1, 1, 1, 1, 1, 5, 3]
def baseStart_2418882 : Nat := 118140960795 + 2418882 * 2 ^ 59
def prefixEnd_2418882 : Nat := 4983230072969 + 3 ^ 40 * 2418882 * 2
def baseEnd_2418882 : Nat := 828032741672606897833847

theorem tailTrace_2418882 : CollatzResearch.WordTrace tailWord_2418882 prefixEnd_2418882 828032741672606897833847 := by
  unfold tailWord_2418882
  simp only [CollatzResearch.WordTrace]
  refine ⟨22055968605702775250292725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58815916281874067334113933 22055968605702775250292725)
  ·
    refine ⟨2067747056784635179714943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22055968605702775250292725 2067747056784635179714943)
    ·
      refine ⟨3101620585176952769572415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2067747056784635179714943 3101620585176952769572415)
      ·
        refine ⟨4652430877765429154358623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3101620585176952769572415 4652430877765429154358623)
        ·
          refine ⟨6978646316648143731537935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4652430877765429154358623 6978646316648143731537935)
          ·
            refine ⟨10467969474972215597306903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6978646316648143731537935 10467969474972215597306903)
            ·
              refine ⟨15701954212458323395960355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10467969474972215597306903 15701954212458323395960355)
              ·
                refine ⟨23552931318687485093940533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15701954212458323395960355 23552931318687485093940533)
                ·
                  refine ⟨2208087311126951727556925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23552931318687485093940533 2208087311126951727556925)
                  ·
                    refine ⟨828032741672606897833847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2208087311126951727556925 828032741672606897833847)
                    ·
                      rfl

theorem cell22_2418882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_2418882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418882 prefixEnd_2418882 := by exact prefixLift 2418882
  have htrace : WordTrace (prefixWord ++ tailWord_2418882) baseStart_2418882 baseEnd_2418882 := by
    simpa [prefixWord, tailWord_2418882, baseEnd_2418882] using wordTrace_append hprefix tailTrace_2418882
  have hstable : (prefixWord ++ tailWord_2418882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418882).length < 2 ^ (prefixWord ++ tailWord_2418882).sum := by decide
  have hdescent : baseEnd_2418882 < baseStart_2418882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418891 : List Nat := [1, 1, 1, 1, 3, 2, 3, 3, 3, 4]
def baseStart_2418891 : Nat := 118140960795 + 2418891 * 2 ^ 59
def prefixEnd_2418891 : Nat := 4983230072969 + 3 ^ 40 * 2418891 * 2
def baseEnd_2418891 : Nat := 828035822556533874358819

theorem tailTrace_2418891 : CollatzResearch.WordTrace tailWord_2418891 prefixEnd_2418891 828035822556533874358819 := by
  unfold tailWord_2418891
  simp only [CollatzResearch.WordTrace]
  refine ⟨88224202679778495538248527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58816135119852330358832351 88224202679778495538248527)
  ·
    refine ⟨132336304019667743307372791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88224202679778495538248527 132336304019667743307372791)
    ·
      refine ⟨198504456029501614961059187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132336304019667743307372791 198504456029501614961059187)
      ·
        refine ⟨297756684044252422441588781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198504456029501614961059187 297756684044252422441588781)
        ·
          refine ⟨111658756516594658415595793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 297756684044252422441588781 111658756516594658415595793)
          ·
            refine ⟨83744067387445993811696845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111658756516594658415595793 83744067387445993811696845)
            ·
              refine ⟨31404025270292247679386317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83744067387445993811696845 31404025270292247679386317)
              ·
                refine ⟨11776509476359592879769869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31404025270292247679386317 11776509476359592879769869)
                ·
                  refine ⟨4416191053634847329913701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11776509476359592879769869 4416191053634847329913701)
                  ·
                    refine ⟨828035822556533874358819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4416191053634847329913701 828035822556533874358819)
                    ·
                      rfl

theorem cell22_2418891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3, 4].length) (baseStart_2418891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418891 prefixEnd_2418891 := by exact prefixLift 2418891
  have htrace : WordTrace (prefixWord ++ tailWord_2418891) baseStart_2418891 baseEnd_2418891 := by
    simpa [prefixWord, tailWord_2418891, baseEnd_2418891] using wordTrace_append hprefix tailTrace_2418891
  have hstable : (prefixWord ++ tailWord_2418891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418891).length < 2 ^ (prefixWord ++ tailWord_2418891).sum := by decide
  have hdescent : baseEnd_2418891 < baseStart_2418891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418923 : List Nat := [1, 1, 1, 1, 2, 5, 1, 6, 4]
def baseStart_2418923 : Nat := 118140960795 + 2418923 * 2 ^ 59
def prefixEnd_2418923 : Nat := 4983230072969 + 3 ^ 40 * 2418923 * 2
def baseEnd_2418923 : Nat := 276015592270165485852907

theorem tailTrace_2418923 : CollatzResearch.WordTrace tailWord_2418923 prefixEnd_2418923 276015592270165485852907 := by
  unfold tailWord_2418923
  simp only [CollatzResearch.WordTrace]
  refine ⟨88225369815662565003413423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58816913210441710002275615 88225369815662565003413423)
  ·
    refine ⟨132338054723493847505120135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88225369815662565003413423 132338054723493847505120135)
    ·
      refine ⟨198507082085240771257680203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132338054723493847505120135 198507082085240771257680203)
      ·
        refine ⟨297760623127861156886520305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198507082085240771257680203 297760623127861156886520305)
        ·
          refine ⟨223320467345895867664890229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 297760623127861156886520305 223320467345895867664890229)
          ·
            refine ⟨20936293813677737593583459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 223320467345895867664890229 20936293813677737593583459)
            ·
              refine ⟨31404440720516606390375189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20936293813677737593583459 31404440720516606390375189)
              ·
                refine ⟨1472083158774215924548837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31404440720516606390375189 1472083158774215924548837)
                ·
                  refine ⟨276015592270165485852907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1472083158774215924548837 276015592270165485852907)
                  ·
                    rfl

theorem cell22_2418923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 6, 4].length) (baseStart_2418923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418923 prefixEnd_2418923 := by exact prefixLift 2418923
  have htrace : WordTrace (prefixWord ++ tailWord_2418923) baseStart_2418923 baseEnd_2418923 := by
    simpa [prefixWord, tailWord_2418923, baseEnd_2418923] using wordTrace_append hprefix tailTrace_2418923
  have hstable : (prefixWord ++ tailWord_2418923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418923).length < 2 ^ (prefixWord ++ tailWord_2418923).sum := by decide
  have hdescent : baseEnd_2418923 < baseStart_2418923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418938 : List Nat := [3, 1, 1, 1, 1, 5, 3, 1, 1, 5]
def baseStart_2418938 : Nat := 118140960795 + 2418938 * 2 ^ 59
def prefixEnd_2418938 : Nat := 4983230072969 + 3 ^ 40 * 2418938 * 2
def baseEnd_2418938 : Nat := 828051911617041418433675

theorem tailTrace_2418938 : CollatzResearch.WordTrace tailWord_2418938 prefixEnd_2418938 828051911617041418433675 := by
  unfold tailWord_2418938
  simp only [CollatzResearch.WordTrace]
  refine ⟨22056479227652055641302367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58817277940405481710139645 22056479227652055641302367)
  ·
    refine ⟨33084718841478083461953551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22056479227652055641302367 33084718841478083461953551)
    ·
      refine ⟨49627078262217125192930327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33084718841478083461953551 49627078262217125192930327)
      ·
        refine ⟨74440617393325687789395491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49627078262217125192930327 74440617393325687789395491)
        ·
          refine ⟨111660926089988531684093237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74440617393325687789395491 111660926089988531684093237)
          ·
            refine ⟨10468211820936424845383741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 111660926089988531684093237 10468211820936424845383741)
            ·
              refine ⟨3925579432851159317018903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10468211820936424845383741 3925579432851159317018903)
              ·
                refine ⟨5888369149276738975528355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3925579432851159317018903 5888369149276738975528355)
                ·
                  refine ⟨8832553723915108463292533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5888369149276738975528355 8832553723915108463292533)
                  ·
                    refine ⟨828051911617041418433675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8832553723915108463292533 828051911617041418433675)
                    ·
                      rfl

theorem cell22_2418938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 1, 5].length) (baseStart_2418938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418938 prefixEnd_2418938 := by exact prefixLift 2418938
  have htrace : WordTrace (prefixWord ++ tailWord_2418938) baseStart_2418938 baseEnd_2418938 := by
    simpa [prefixWord, tailWord_2418938, baseEnd_2418938] using wordTrace_append hprefix tailTrace_2418938
  have hstable : (prefixWord ++ tailWord_2418938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418938).length < 2 ^ (prefixWord ++ tailWord_2418938).sum := by decide
  have hdescent : baseEnd_2418938 < baseStart_2418938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418970 : List Nat := [3, 1, 1, 3, 4, 1, 1, 2, 2, 4]
def baseStart_2418970 : Nat := 118140960795 + 2418970 * 2 ^ 59
def prefixEnd_2418970 : Nat := 4983230072969 + 3 ^ 40 * 2418970 * 2
def baseEnd_2418970 : Nat := 828062865871004001633577

theorem tailTrace_2418970 : CollatzResearch.WordTrace tailWord_2418970 prefixEnd_2418970 828062865871004001633577 := by
  unfold tailWord_2418970
  simp only [CollatzResearch.WordTrace]
  refine ⟨22056771011623073007593591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58818056030994861353582909 22056771011623073007593591)
  ·
    refine ⟨33085156517434609511390387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22056771011623073007593591 33085156517434609511390387)
    ·
      refine ⟨49627734776151914267085581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33085156517434609511390387 49627734776151914267085581)
      ·
        refine ⟨18610400541056967850157093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49627734776151914267085581 18610400541056967850157093)
        ·
          refine ⟨3489450101448181471904455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18610400541056967850157093 3489450101448181471904455)
          ·
            refine ⟨5234175152172272207856683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3489450101448181471904455 5234175152172272207856683)
            ·
              refine ⟨7851262728258408311785025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5234175152172272207856683 7851262728258408311785025)
              ·
                refine ⟨5888447046193806233838769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7851262728258408311785025 5888447046193806233838769)
                ·
                  refine ⟨4416335284645354675379077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5888447046193806233838769 4416335284645354675379077)
                  ·
                    refine ⟨828062865871004001633577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4416335284645354675379077 828062865871004001633577)
                    ·
                      rfl

theorem cell22_2418970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 2, 4].length) (baseStart_2418970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418970 prefixEnd_2418970 := by exact prefixLift 2418970
  have htrace : WordTrace (prefixWord ++ tailWord_2418970) baseStart_2418970 baseEnd_2418970 := by
    simpa [prefixWord, tailWord_2418970, baseEnd_2418970] using wordTrace_append hprefix tailTrace_2418970
  have hstable : (prefixWord ++ tailWord_2418970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418970).length < 2 ^ (prefixWord ++ tailWord_2418970).sum := by decide
  have hdescent : baseEnd_2418970 < baseStart_2418970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418989 : List Nat := [1, 5, 3, 1, 2, 1, 1, 3, 2, 3]
def baseStart_2418989 : Nat := 118140960795 + 2418989 * 2 ^ 59
def prefixEnd_2418989 : Nat := 4983230072969 + 3 ^ 40 * 2418989 * 2
def baseEnd_2418989 : Nat := 828069369959294285408519

theorem tailTrace_2418989 : CollatzResearch.WordTrace tailWord_2418989 prefixEnd_2418989 828069369959294285408519 := by
  unfold tailWord_2418989
  simp only [CollatzResearch.WordTrace]
  refine ⟨88227777033423458275316021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58818518022282305516877347 88227777033423458275316021)
  ·
    refine ⟨8271354096883449213310877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88227777033423458275316021 8271354096883449213310877)
    ·
      refine ⟨3101757786331293454991579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8271354096883449213310877 3101757786331293454991579)
      ·
        refine ⟨4652636679496940182487369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3101757786331293454991579 4652636679496940182487369)
        ·
          refine ⟨3489477509622705136865527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4652636679496940182487369 3489477509622705136865527)
          ·
            refine ⟨5234216264434057705298291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3489477509622705136865527 5234216264434057705298291)
            ·
              refine ⟨7851324396651086557947437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5234216264434057705298291 7851324396651086557947437)
              ·
                refine ⟨2944246648744157459230289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7851324396651086557947437 2944246648744157459230289)
                ·
                  refine ⟨2208184986558118094422717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2944246648744157459230289 2208184986558118094422717)
                  ·
                    refine ⟨828069369959294285408519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2208184986558118094422717 828069369959294285408519)
                    ·
                      rfl

theorem cell22_2418989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_2418989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2418989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2418989 prefixEnd_2418989 := by exact prefixLift 2418989
  have htrace : WordTrace (prefixWord ++ tailWord_2418989) baseStart_2418989 baseEnd_2418989 := by
    simpa [prefixWord, tailWord_2418989, baseEnd_2418989] using wordTrace_append hprefix tailTrace_2418989
  have hstable : (prefixWord ++ tailWord_2418989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418989).length < 2 ^ (prefixWord ++ tailWord_2418989).sum := by decide
  have hdescent : baseEnd_2418989 < baseStart_2418989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419043 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 5, 4]
def baseStart_2419043 : Nat := 118140960795 + 2419043 * 2 ^ 59
def prefixEnd_2419043 : Nat := 4983230072969 + 3 ^ 40 * 2419043 * 2
def baseEnd_2419043 : Nat := 828087855262856144558353

theorem tailTrace_2419043 : CollatzResearch.WordTrace tailWord_2419043 prefixEnd_2419043 828087855262856144558353 := by
  unfold tailWord_2419043
  simp only [CollatzResearch.WordTrace]
  refine ⟨88229746575227825497781783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58819831050151883665187855 88229746575227825497781783)
  ·
    refine ⟨132344619862841738246672675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88229746575227825497781783 132344619862841738246672675)
    ·
      refine ⟨198516929794262607370009013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132344619862841738246672675 198516929794262607370009013)
      ·
        refine ⟨18610962168212119440938345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 198516929794262607370009013 18610962168212119440938345)
        ·
          refine ⟨13958221626159089580703759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18610962168212119440938345 13958221626159089580703759)
          ·
            refine ⟨20937332439238634371055639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13958221626159089580703759 20937332439238634371055639)
            ·
              refine ⟨31405998658857951556583459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20937332439238634371055639 31405998658857951556583459)
              ·
                refine ⟨47108997988286927334875189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31405998658857951556583459 47108997988286927334875189)
                ·
                  refine ⟨4416468561401899437644549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47108997988286927334875189 4416468561401899437644549)
                  ·
                    refine ⟨828087855262856144558353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4416468561401899437644549 828087855262856144558353)
                    ·
                      rfl

theorem cell22_2419043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5, 4].length) (baseStart_2419043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2419043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2419043 prefixEnd_2419043 := by exact prefixLift 2419043
  have htrace : WordTrace (prefixWord ++ tailWord_2419043) baseStart_2419043 baseEnd_2419043 := by
    simpa [prefixWord, tailWord_2419043, baseEnd_2419043] using wordTrace_append hprefix tailTrace_2419043
  have hstable : (prefixWord ++ tailWord_2419043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419043).length < 2 ^ (prefixWord ++ tailWord_2419043).sum := by decide
  have hdescent : baseEnd_2419043 < baseStart_2419043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419058 : List Nat := [3, 2, 1, 2, 1, 3, 1, 1, 8]
def baseStart_2419058 : Nat := 118140960795 + 2419058 * 2 ^ 59
def prefixEnd_2419058 : Nat := 4983230072969 + 3 ^ 40 * 2419058 * 2
def baseEnd_2419058 : Nat := 276030996689800368477769

theorem tailTrace_2419058 : CollatzResearch.WordTrace tailWord_2419058 prefixEnd_2419058 276030996689800368477769 := by
  unfold tailWord_2419058
  simp only [CollatzResearch.WordTrace]
  refine ⟨22057573417543370764894457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58820195780115655373051885 22057573417543370764894457)
  ·
    refine ⟨16543180063157528073670843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22057573417543370764894457 16543180063157528073670843)
    ·
      refine ⟨24814770094736292110506265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16543180063157528073670843 24814770094736292110506265)
      ·
        refine ⟨18611077571052219082879699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24814770094736292110506265 18611077571052219082879699)
        ·
          refine ⟨27916616356578328624319549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18611077571052219082879699 27916616356578328624319549)
          ·
            refine ⟨10468731133716873234119831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27916616356578328624319549 10468731133716873234119831)
            ·
              refine ⟨15703096700575309851179747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10468731133716873234119831 15703096700575309851179747)
              ·
                refine ⟨23554645050862964776769621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15703096700575309851179747 23554645050862964776769621)
                ·
                  refine ⟨276030996689800368477769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23554645050862964776769621 276030996689800368477769)
                  ·
                    rfl

theorem cell22_2419058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_2419058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2419058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2419058 prefixEnd_2419058 := by exact prefixLift 2419058
  have htrace : WordTrace (prefixWord ++ tailWord_2419058) baseStart_2419058 baseEnd_2419058 := by
    simpa [prefixWord, tailWord_2419058, baseEnd_2419058] using wordTrace_append hprefix tailTrace_2419058
  have hstable : (prefixWord ++ tailWord_2419058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419058).length < 2 ^ (prefixWord ++ tailWord_2419058).sum := by decide
  have hdescent : baseEnd_2419058 < baseStart_2419058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419092 : List Nat := [2, 4, 2, 1, 3, 1, 2, 1, 6]
def baseStart_2419092 : Nat := 118140960795 + 2419092 * 2 ^ 59
def prefixEnd_2419092 : Nat := 4983230072969 + 3 ^ 40 * 2419092 * 2
def baseEnd_2419092 : Nat := 276034876321412116694401

theorem tailTrace_2419092 : CollatzResearch.WordTrace tailWord_2419092 prefixEnd_2419092 276034876321412116694401 := by
  unfold tailWord_2419092
  simp only [CollatzResearch.WordTrace]
  refine ⟨44115766876025153433157765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58821022501366871244210353 44115766876025153433157765)
  ·
    refine ⟨8271706289254716268717081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44115766876025153433157765 8271706289254716268717081)
    ·
      refine ⟨6203779716941037201537811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8271706289254716268717081 6203779716941037201537811)
      ·
        refine ⟨9305669575411555802306717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6203779716941037201537811 9305669575411555802306717)
        ·
          refine ⟨3489626090779333425865019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9305669575411555802306717 3489626090779333425865019)
          ·
            refine ⟨5234439136169000138797529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3489626090779333425865019 5234439136169000138797529)
            ·
              refine ⟨3925829352126750104098147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5234439136169000138797529 3925829352126750104098147)
              ·
                refine ⟨5888744028190125156147221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3925829352126750104098147 5888744028190125156147221)
                ·
                  refine ⟨276034876321412116694401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5888744028190125156147221 276034876321412116694401)
                  ·
                    rfl

theorem cell22_2419092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_2419092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2419092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2419092 prefixEnd_2419092 := by exact prefixLift 2419092
  have htrace : WordTrace (prefixWord ++ tailWord_2419092) baseStart_2419092 baseEnd_2419092 := by
    simpa [prefixWord, tailWord_2419092, baseEnd_2419092] using wordTrace_append hprefix tailTrace_2419092
  have hstable : (prefixWord ++ tailWord_2419092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419092).length < 2 ^ (prefixWord ++ tailWord_2419092).sum := by decide
  have hdescent : baseEnd_2419092 < baseStart_2419092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419103 : List Nat := [1, 1, 2, 5, 1, 1, 2, 9]
def baseStart_2419103 : Nat := 118140960795 + 2419103 * 2 ^ 59
def prefixEnd_2419103 : Nat := 4983230072969 + 3 ^ 40 * 2419103 * 2
def baseEnd_2419103 : Nat := 92012043832115109784241

theorem tailTrace_2419103 : CollatzResearch.WordTrace tailWord_2419103 prefixEnd_2419103 92012043832115109784241 := by
  unfold tailWord_2419103
  simp only [CollatzResearch.WordTrace]
  refine ⟨88231934955010455744965963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58821289970006970496643975 88231934955010455744965963)
  ·
    refine ⟨132347902432515683617448945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88231934955010455744965963 132347902432515683617448945)
    ·
      refine ⟨99260926824386762713086709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132347902432515683617448945 99260926824386762713086709)
      ·
        refine ⟨9305711889786259004351879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 99260926824386762713086709 9305711889786259004351879)
        ·
          refine ⟨13958567834679388506527819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9305711889786259004351879 13958567834679388506527819)
          ·
            refine ⟨20937851752019082759791729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13958567834679388506527819 20937851752019082759791729)
            ·
              refine ⟨15703388814014312069843797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20937851752019082759791729 15703388814014312069843797)
              ·
                refine ⟨92012043832115109784241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15703388814014312069843797 92012043832115109784241)
                ·
                  rfl

theorem cell22_2419103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 9].length) (baseStart_2419103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2419103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2419103 prefixEnd_2419103 := by exact prefixLift 2419103
  have htrace : WordTrace (prefixWord ++ tailWord_2419103) baseStart_2419103 baseEnd_2419103 := by
    simpa [prefixWord, tailWord_2419103, baseEnd_2419103] using wordTrace_append hprefix tailTrace_2419103
  have hstable : (prefixWord ++ tailWord_2419103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419103).length < 2 ^ (prefixWord ++ tailWord_2419103).sum := by decide
  have hdescent : baseEnd_2419103 < baseStart_2419103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419210 : List Nat := [3, 1, 2, 2, 2, 1, 2, 3, 6]
def baseStart_2419210 : Nat := 118140960795 + 2419210 * 2 ^ 59
def prefixEnd_2419210 : Nat := 4983230072969 + 3 ^ 40 * 2419210 * 2
def baseEnd_2419210 : Nat := 276048340925241125210947

theorem tailTrace_2419210 : CollatzResearch.WordTrace tailWord_2419210 prefixEnd_2419210 276048340925241125210947 := by
  unfold tailWord_2419210
  simp only [CollatzResearch.WordTrace]
  refine ⟨22058959391405703254777771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58823891710415208679407389 22058959391405703254777771)
  ·
    refine ⟨33088439087108554882166657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22058959391405703254777771 33088439087108554882166657)
    ·
      refine ⟨24816329315331416161624993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33088439087108554882166657 24816329315331416161624993)
      ·
        refine ⟨18612246986498562121218745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24816329315331416161624993 18612246986498562121218745)
        ·
          refine ⟨13959185239873921590914059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18612246986498562121218745 13959185239873921590914059)
          ·
            refine ⟨20938777859810882386371089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13959185239873921590914059 20938777859810882386371089)
            ·
              refine ⟨15704083394858161789778317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20938777859810882386371089 15704083394858161789778317)
              ·
                refine ⟨5889031273071810671166869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15704083394858161789778317 5889031273071810671166869)
                ·
                  refine ⟨276048340925241125210947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5889031273071810671166869 276048340925241125210947)
                  ·
                    rfl

theorem cell22_2419210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 6].length) (baseStart_2419210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2419210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2419210 prefixEnd_2419210 := by exact prefixLift 2419210
  have htrace : WordTrace (prefixWord ++ tailWord_2419210) baseStart_2419210 baseEnd_2419210 := by
    simpa [prefixWord, tailWord_2419210, baseEnd_2419210] using wordTrace_append hprefix tailTrace_2419210
  have hstable : (prefixWord ++ tailWord_2419210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419210).length < 2 ^ (prefixWord ++ tailWord_2419210).sum := by decide
  have hdescent : baseEnd_2419210 < baseStart_2419210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419242 : List Nat := [3, 1, 4, 1, 1, 2, 2, 2, 1, 5]
def baseStart_2419242 : Nat := 118140960795 + 2419242 * 2 ^ 59
def prefixEnd_2419242 : Nat := 4983230072969 + 3 ^ 40 * 2419242 * 2
def baseEnd_2419242 : Nat := 828155977029685958832743

theorem tailTrace_2419242 : CollatzResearch.WordTrace tailWord_2419242 prefixEnd_2419242 828155977029685958832743 := by
  unfold tailWord_2419242
  simp only [CollatzResearch.WordTrace]
  refine ⟨22059251175376720621068995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58824669801004588322850653 22059251175376720621068995)
  ·
    refine ⟨33088876763065080931603493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22059251175376720621068995 33088876763065080931603493)
    ·
      refine ⟨6204164393074702674675655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33088876763065080931603493 6204164393074702674675655)
      ·
        refine ⟨9306246589612054012013483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6204164393074702674675655 9306246589612054012013483)
        ·
          refine ⟨13959369884418081018020225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9306246589612054012013483 13959369884418081018020225)
          ·
            refine ⟨10469527413313560763515169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13959369884418081018020225 10469527413313560763515169)
            ·
              refine ⟨7852145559985170572636377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10469527413313560763515169 7852145559985170572636377)
              ·
                refine ⟨5889109169988877929477283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7852145559985170572636377 5889109169988877929477283)
                ·
                  refine ⟨8833663754983316894215925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5889109169988877929477283 8833663754983316894215925)
                  ·
                    refine ⟨828155977029685958832743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8833663754983316894215925 828155977029685958832743)
                    ·
                      rfl

theorem cell22_2419242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_2419242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2419242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2419242 prefixEnd_2419242 := by exact prefixLift 2419242
  have htrace : WordTrace (prefixWord ++ tailWord_2419242) baseStart_2419242 baseEnd_2419242 := by
    simpa [prefixWord, tailWord_2419242, baseEnd_2419242] using wordTrace_append hprefix tailTrace_2419242
  have hstable : (prefixWord ++ tailWord_2419242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419242).length < 2 ^ (prefixWord ++ tailWord_2419242).sum := by decide
  have hdescent : baseEnd_2419242 < baseStart_2419242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419285 : List Nat := [1, 3, 2, 2, 1, 1, 2, 2, 2, 6]
def baseStart_2419285 : Nat := 118140960795 + 2419285 * 2 ^ 59
def prefixEnd_2419285 : Nat := 4983230072969 + 3 ^ 40 * 2419285 * 2
def baseEnd_2419285 : Nat := 828170696808448180007611

theorem tailTrace_2419285 : CollatzResearch.WordTrace tailWord_2419285 prefixEnd_2419285 828170696808448180007611 := by
  unfold tailWord_2419285
  simp only [CollatzResearch.WordTrace]
  refine ⟨88238573040351100828091309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58825715360234067218727539 88238573040351100828091309)
  ·
    refine ⟨33089464890131662810534241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88238573040351100828091309 33089464890131662810534241)
    ·
      refine ⟨24817098667598747107900681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33089464890131662810534241 24817098667598747107900681)
      ·
        refine ⟨18612824000699060330925511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24817098667598747107900681 18612824000699060330925511)
        ·
          refine ⟨27919236001048590496388267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18612824000699060330925511 27919236001048590496388267)
          ·
            refine ⟨41878854001572885744582401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27919236001048590496388267 41878854001572885744582401)
            ·
              refine ⟨31409140501179664308436801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41878854001572885744582401 31409140501179664308436801)
              ·
                refine ⟨23556855375884748231327601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31409140501179664308436801 23556855375884748231327601)
                ·
                  refine ⟨17667641531913561173495701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23556855375884748231327601 17667641531913561173495701)
                  ·
                    refine ⟨828170696808448180007611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17667641531913561173495701 828170696808448180007611)
                    ·
                      rfl

theorem cell22_2419285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_2419285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2419285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2419285 prefixEnd_2419285 := by exact prefixLift 2419285
  have htrace : WordTrace (prefixWord ++ tailWord_2419285) baseStart_2419285 baseEnd_2419285 := by
    simpa [prefixWord, tailWord_2419285, baseEnd_2419285] using wordTrace_append hprefix tailTrace_2419285
  have hstable : (prefixWord ++ tailWord_2419285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419285).length < 2 ^ (prefixWord ++ tailWord_2419285).sum := by decide
  have hdescent : baseEnd_2419285 < baseStart_2419285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419287 : List Nat := [1, 1, 3, 2, 2, 2, 1, 4, 3, 3]
def baseStart_2419287 : Nat := 118140960795 + 2419287 * 2 ^ 59
def prefixEnd_2419287 : Nat := 4983230072969 + 3 ^ 40 * 2419287 * 2
def baseEnd_2419287 : Nat := 828171381449320841457605

theorem tailTrace_2419287 : CollatzResearch.WordTrace tailWord_2419287 prefixEnd_2419287 828171381449320841457605 := by
  unfold tailWord_2419287
  simp only [CollatzResearch.WordTrace]
  refine ⟨88238645986343855169664115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58825763990895903446442743 88238645986343855169664115)
  ·
    refine ⟨132357968979515782754496173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88238645986343855169664115 132357968979515782754496173)
    ·
      refine ⟨49634238367318418532936065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132357968979515782754496173 49634238367318418532936065)
      ·
        refine ⟨37225678775488813899702049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49634238367318418532936065 37225678775488813899702049)
        ·
          refine ⟨27919259081616610424776537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37225678775488813899702049 27919259081616610424776537)
          ·
            refine ⟨20939444311212457818582403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27919259081616610424776537 20939444311212457818582403)
            ·
              refine ⟨31409166466818686727873605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20939444311212457818582403 31409166466818686727873605)
              ·
                refine ⟨5889218712528503761476301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31409166466818686727873605 5889218712528503761476301)
                ·
                  refine ⟨2208457017198188910553613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5889218712528503761476301 2208457017198188910553613)
                  ·
                    refine ⟨828171381449320841457605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2208457017198188910553613 828171381449320841457605)
                    ·
                      rfl

theorem cell22_2419287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 3, 3].length) (baseStart_2419287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2419287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2419287 prefixEnd_2419287 := by exact prefixLift 2419287
  have htrace : WordTrace (prefixWord ++ tailWord_2419287) baseStart_2419287 baseEnd_2419287 := by
    simpa [prefixWord, tailWord_2419287, baseEnd_2419287] using wordTrace_append hprefix tailTrace_2419287
  have hstable : (prefixWord ++ tailWord_2419287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419287).length < 2 ^ (prefixWord ++ tailWord_2419287).sum := by decide
  have hdescent : baseEnd_2419287 < baseStart_2419287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419300 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 9]
def baseStart_2419300 : Nat := 118140960795 + 2419300 * 2 ^ 59
def prefixEnd_2419300 : Nat := 4983230072969 + 3 ^ 40 * 2419300 * 2
def baseEnd_2419300 : Nat := 276058610538331046960855

theorem tailTrace_2419300 : CollatzResearch.WordTrace tailWord_2419300 prefixEnd_2419300 276058610538331046960855 := by
  unfold tailWord_2419300
  simp only [CollatzResearch.WordTrace]
  refine ⟨44119560067648379194943677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58826080090197838926591569 44119560067648379194943677)
  ·
    refine ⟨16544835025368142198103879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44119560067648379194943677 16544835025368142198103879)
    ·
      refine ⟨24817252538052213297155819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16544835025368142198103879 24817252538052213297155819)
      ·
        refine ⟨37225878807078319945733729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24817252538052213297155819 37225878807078319945733729)
        ·
          refine ⟨27919409105308739959300297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37225878807078319945733729 27919409105308739959300297)
          ·
            refine ⟨20939556828981554969475223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27919409105308739959300297 20939556828981554969475223)
            ·
              refine ⟨31409335243472332454212835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20939556828981554969475223 31409335243472332454212835)
              ·
                refine ⟨47114002865208498681319253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31409335243472332454212835 47114002865208498681319253)
                ·
                  refine ⟨276058610538331046960855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 47114002865208498681319253 276058610538331046960855)
                  ·
                    rfl

theorem cell22_2419300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_2419300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2419300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2419300 prefixEnd_2419300 := by exact prefixLift 2419300
  have htrace : WordTrace (prefixWord ++ tailWord_2419300) baseStart_2419300 baseEnd_2419300 := by
    simpa [prefixWord, tailWord_2419300, baseEnd_2419300] using wordTrace_append hprefix tailTrace_2419300
  have hstable : (prefixWord ++ tailWord_2419300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419300).length < 2 ^ (prefixWord ++ tailWord_2419300).sum := by decide
  have hdescent : baseEnd_2419300 < baseStart_2419300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419315 : List Nat := [1, 1, 1, 2, 2, 1, 1, 6, 2, 5]
def baseStart_2419315 : Nat := 118140960795 + 2419315 * 2 ^ 59
def prefixEnd_2419315 : Nat := 4983230072969 + 3 ^ 40 * 2419315 * 2
def baseEnd_2419315 : Nat := 828180966421538101757519

theorem tailTrace_2419315 : CollatzResearch.WordTrace tailWord_2419315 prefixEnd_2419315 828180966421538101757519 := by
  unfold tailWord_2419315
  simp only [CollatzResearch.WordTrace]
  refine ⟨88239667230242415951683399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58826444820161610634455599 88239667230242415951683399)
  ·
    refine ⟨132359500845363623927525099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88239667230242415951683399 132359500845363623927525099)
    ·
      refine ⟨198539251268045435891287649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132359500845363623927525099 198539251268045435891287649)
      ·
        refine ⟨148904438451034076918465737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198539251268045435891287649 148904438451034076918465737)
        ·
          refine ⟨111678328838275557688849303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148904438451034076918465737 111678328838275557688849303)
          ·
            refine ⟨167517493257413336533273955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111678328838275557688849303 167517493257413336533273955)
            ·
              refine ⟨251276239886120004799910933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167517493257413336533273955 251276239886120004799910933)
              ·
                refine ⟨11778573744661875224995825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 251276239886120004799910933 11778573744661875224995825)
                ·
                  refine ⟨8833930308496406418746869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11778573744661875224995825 8833930308496406418746869)
                  ·
                    refine ⟨828180966421538101757519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8833930308496406418746869 828180966421538101757519)
                    ·
                      rfl

theorem cell22_2419315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 5].length) (baseStart_2419315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2419315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2419315 prefixEnd_2419315 := by exact prefixLift 2419315
  have htrace : WordTrace (prefixWord ++ tailWord_2419315) baseStart_2419315 baseEnd_2419315 := by
    simpa [prefixWord, tailWord_2419315, baseEnd_2419315] using wordTrace_append hprefix tailTrace_2419315
  have hstable : (prefixWord ++ tailWord_2419315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419315).length < 2 ^ (prefixWord ++ tailWord_2419315).sum := by decide
  have hdescent : baseEnd_2419315 < baseStart_2419315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419379 : List Nat := [1, 1, 1, 2, 3, 5, 1, 4, 4]
def baseStart_2419379 : Nat := 118140960795 + 2419379 * 2 ^ 59
def prefixEnd_2419379 : Nat := 4983230072969 + 3 ^ 40 * 2419379 * 2
def baseEnd_2419379 : Nat := 276067624976487756052441

theorem tailTrace_2419379 : CollatzResearch.WordTrace tailWord_2419379 prefixEnd_2419379 276067624976487756052441 := by
  unfold tailWord_2419379
  simp only [CollatzResearch.WordTrace]
  refine ⟨88242001502010554882013191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58828001001340369921342127 88242001502010554882013191)
  ·
    refine ⟨132363002253015832323019787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88242001502010554882013191 132363002253015832323019787)
    ·
      refine ⟨198544503379523748484529681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132363002253015832323019787 198544503379523748484529681)
      ·
        refine ⟨148908377534642811363397261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198544503379523748484529681 148908377534642811363397261)
        ·
          refine ⟨55840641575491054261273973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148908377534642811363397261 55840641575491054261273973)
          ·
            refine ⟨5235060147702286336994435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55840641575491054261273973 5235060147702286336994435)
            ·
              refine ⟨7852590221553429505491653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5235060147702286336994435 7852590221553429505491653)
              ·
                refine ⟨1472360666541268032279685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7852590221553429505491653 1472360666541268032279685)
                ·
                  refine ⟨276067624976487756052441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1472360666541268032279685 276067624976487756052441)
                  ·
                    rfl

theorem cell22_2419379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 4, 4].length) (baseStart_2419379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2419379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2419379 prefixEnd_2419379 := by exact prefixLift 2419379
  have htrace : WordTrace (prefixWord ++ tailWord_2419379) baseStart_2419379 baseEnd_2419379 := by
    simpa [prefixWord, tailWord_2419379, baseEnd_2419379] using wordTrace_append hprefix tailTrace_2419379
  have hstable : (prefixWord ++ tailWord_2419379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419379).length < 2 ^ (prefixWord ++ tailWord_2419379).sum := by decide
  have hdescent : baseEnd_2419379 < baseStart_2419379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419413 : List Nat := [1, 3, 2, 5, 1, 1, 2, 3, 4]
def baseStart_2419413 : Nat := 118140960795 + 2419413 * 2 ^ 59
def prefixEnd_2419413 : Nat := 4983230072969 + 3 ^ 40 * 2419413 * 2
def baseEnd_2419413 : Nat := 276071504608099504269073

theorem tailTrace_2419413 : CollatzResearch.WordTrace tailWord_2419413 prefixEnd_2419413 276071504608099504269073 := by
  unfold tailWord_2419413
  simp only [CollatzResearch.WordTrace]
  refine ⟨88243241583887378688750893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58828827722591585792500595 88243241583887378688750893)
  ·
    refine ⟨33091215593957767008281585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88243241583887378688750893 33091215593957767008281585)
    ·
      refine ⟨24818411695468325256211189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33091215593957767008281585 24818411695468325256211189)
      ·
        refine ⟨2326726096450155492769799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24818411695468325256211189 2326726096450155492769799)
        ·
          refine ⟨3490089144675233239154699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2326726096450155492769799 3490089144675233239154699)
          ·
            refine ⟨5235133717012849858732049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3490089144675233239154699 5235133717012849858732049)
            ·
              refine ⟨3926350287759637394049037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5235133717012849858732049 3926350287759637394049037)
              ·
                refine ⟨1472381357909864022768389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3926350287759637394049037 1472381357909864022768389)
                ·
                  refine ⟨276071504608099504269073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1472381357909864022768389 276071504608099504269073)
                  ·
                    rfl

theorem cell22_2419413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 3, 4].length) (baseStart_2419413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2419413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2419413 prefixEnd_2419413 := by exact prefixLift 2419413
  have htrace : WordTrace (prefixWord ++ tailWord_2419413) baseStart_2419413 baseEnd_2419413 := by
    simpa [prefixWord, tailWord_2419413, baseEnd_2419413] using wordTrace_append hprefix tailTrace_2419413
  have hstable : (prefixWord ++ tailWord_2419413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419413).length < 2 ^ (prefixWord ++ tailWord_2419413).sum := by decide
  have hdescent : baseEnd_2419413 < baseStart_2419413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419439 : List Nat := [1, 1, 2, 1, 5, 2, 1, 3, 3, 3]
def baseStart_2419439 : Nat := 118140960795 + 2419439 * 2 ^ 59
def prefixEnd_2419439 : Nat := 4983230072969 + 3 ^ 40 * 2419439 * 2
def baseEnd_2419439 : Nat := 828223414155643111657139

theorem tailTrace_2419439 : CollatzResearch.WordTrace tailWord_2419439 prefixEnd_2419439 828223414155643111657139 := by
  unfold tailWord_2419439
  simp only [CollatzResearch.WordTrace]
  refine ⟨88244189881793185129197371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58829459921195456752798247 88244189881793185129197371)
  ·
    refine ⟨132366284822689777693796057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88244189881793185129197371 132366284822689777693796057)
    ·
      refine ⟨99274713617017333270347043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132366284822689777693796057 99274713617017333270347043)
      ·
        refine ⟨148912070425525999905520565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99274713617017333270347043 148912070425525999905520565)
        ·
          refine ⟨13960506602393062491142553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 148912070425525999905520565 13960506602393062491142553)
          ·
            refine ⟨10470379951794796868356915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13960506602393062491142553 10470379951794796868356915)
            ·
              refine ⟨15705569927692195302535373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10470379951794796868356915 15705569927692195302535373)
              ·
                refine ⟨5889588722884573238450765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15705569927692195302535373 5889588722884573238450765)
                ·
                  refine ⟨2208595771081714964419037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5889588722884573238450765 2208595771081714964419037)
                  ·
                    refine ⟨828223414155643111657139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2208595771081714964419037 828223414155643111657139)
                    ·
                      rfl

theorem cell22_2419439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 3, 3].length) (baseStart_2419439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2419439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2419439 prefixEnd_2419439 := by exact prefixLift 2419439
  have htrace : WordTrace (prefixWord ++ tailWord_2419439) baseStart_2419439 baseEnd_2419439 := by
    simpa [prefixWord, tailWord_2419439, baseEnd_2419439] using wordTrace_append hprefix tailTrace_2419439
  have hstable : (prefixWord ++ tailWord_2419439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419439).length < 2 ^ (prefixWord ++ tailWord_2419439).sum := by decide
  have hdescent : baseEnd_2419439 < baseStart_2419439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419445 : List Nat := [1, 3, 6, 1, 1, 2, 1, 1, 1, 5]
def baseStart_2419445 : Nat := 118140960795 + 2419445 * 2 ^ 59
def prefixEnd_2419445 : Nat := 4983230072969 + 3 ^ 40 * 2419445 * 2
def baseEnd_2419445 : Nat := 828225468078261096007121

theorem tailTrace_2419445 : CollatzResearch.WordTrace tailWord_2419445 prefixEnd_2419445 828225468078261096007121 := by
  unfold tailWord_2419445
  simp only [CollatzResearch.WordTrace]
  refine ⟨88244408719771448153915789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58829605813180965435943859 88244408719771448153915789)
  ·
    refine ⟨33091653269914293057718421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88244408719771448153915789 33091653269914293057718421)
    ·
      refine ⟨1551171247027232487080551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 33091653269914293057718421 1551171247027232487080551)
      ·
        refine ⟨2326756870540848730620827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1551171247027232487080551 2326756870540848730620827)
        ·
          refine ⟨3490135305811273095931241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2326756870540848730620827 3490135305811273095931241)
          ·
            refine ⟨2617601479358454821948431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3490135305811273095931241 2617601479358454821948431)
            ·
              refine ⟨3926402219037682232922647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2617601479358454821948431 3926402219037682232922647)
              ·
                refine ⟨5889603328556523349383971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3926402219037682232922647 5889603328556523349383971)
                ·
                  refine ⟨8834404992834785024075957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5889603328556523349383971 8834404992834785024075957)
                  ·
                    refine ⟨828225468078261096007121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8834404992834785024075957 828225468078261096007121)
                    ·
                      rfl

theorem cell22_2419445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_2419445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2419445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2419445 prefixEnd_2419445 := by exact prefixLift 2419445
  have htrace : WordTrace (prefixWord ++ tailWord_2419445) baseStart_2419445 baseEnd_2419445 := by
    simpa [prefixWord, tailWord_2419445, baseEnd_2419445] using wordTrace_append hprefix tailTrace_2419445
  have hstable : (prefixWord ++ tailWord_2419445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419445).length < 2 ^ (prefixWord ++ tailWord_2419445).sum := by decide
  have hdescent : baseEnd_2419445 < baseStart_2419445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419490 : List Nat := [3, 3, 1, 1, 2, 3, 3, 2, 1, 3]
def baseStart_2419490 : Nat := 118140960795 + 2419490 * 2 ^ 59
def prefixEnd_2419490 : Nat := 4983230072969 + 3 ^ 40 * 2419490 * 2
def baseEnd_2419490 : Nat := 828240872497895978631983

theorem tailTrace_2419490 : CollatzResearch.WordTrace tailWord_2419490 prefixEnd_2419490 828240872497895978631983 := by
  unfold tailWord_2419490
  simp only [CollatzResearch.WordTrace]
  refine ⟨22061512501152105209825981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58830700003072280559535949 22061512501152105209825981)
  ·
    refine ⟨8273067187932039453684743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22061512501152105209825981 8273067187932039453684743)
    ·
      refine ⟨12409600781898059180527115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8273067187932039453684743 12409600781898059180527115)
      ·
        refine ⟨18614401172847088770790673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12409600781898059180527115 18614401172847088770790673)
        ·
          refine ⟨13960800879635316578093005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18614401172847088770790673 13960800879635316578093005)
          ·
            refine ⟨5235300329863243716784877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13960800879635316578093005 5235300329863243716784877)
            ·
              refine ⟨1963237623698716393794329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5235300329863243716784877 1963237623698716393794329)
              ·
                refine ⟨1472428217774037295345747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1963237623698716393794329 1472428217774037295345747)
                ·
                  refine ⟨2208642326661055943018621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1472428217774037295345747 2208642326661055943018621)
                  ·
                    refine ⟨828240872497895978631983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2208642326661055943018621 828240872497895978631983)
                    ·
                      rfl

theorem cell22_2419490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_2419490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2419490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2419490 prefixEnd_2419490 := by exact prefixLift 2419490
  have htrace : WordTrace (prefixWord ++ tailWord_2419490) baseStart_2419490 baseEnd_2419490 := by
    simpa [prefixWord, tailWord_2419490, baseEnd_2419490] using wordTrace_append hprefix tailTrace_2419490
  have hstable : (prefixWord ++ tailWord_2419490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419490).length < 2 ^ (prefixWord ++ tailWord_2419490).sum := by decide
  have hdescent : baseEnd_2419490 < baseStart_2419490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419529 : List Nat := [1, 2, 1, 1, 2, 6, 1, 2, 1, 5]
def baseStart_2419529 : Nat := 118140960795 + 2419529 * 2 ^ 59
def prefixEnd_2419529 : Nat := 4983230072969 + 3 ^ 40 * 2419529 * 2
def baseEnd_2419529 : Nat := 828254222994912876906863

theorem tailTrace_2419529 : CollatzResearch.WordTrace tailWord_2419529 prefixEnd_2419529 828254222994912876906863 := by
  unfold tailWord_2419529
  simp only [CollatzResearch.WordTrace]
  refine ⟨88247472451467130499973641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58831648300978086999982427 88247472451467130499973641)
  ·
    refine ⟨66185604338600347874980231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88247472451467130499973641 66185604338600347874980231)
    ·
      refine ⟨99278406507900521812470347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66185604338600347874980231 99278406507900521812470347)
      ·
        refine ⟨148917609761850782718705521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99278406507900521812470347 148917609761850782718705521)
        ·
          refine ⟨111688207321388087039029141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148917609761850782718705521 111688207321388087039029141)
          ·
            refine ⟨5235384718190066579954491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 111688207321388087039029141 5235384718190066579954491)
            ·
              refine ⟨7853077077285099869931737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5235384718190066579954491 7853077077285099869931737)
              ·
                refine ⟨5889807807963824902448803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7853077077285099869931737 5889807807963824902448803)
                ·
                  refine ⟨8834711711945737353673205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5889807807963824902448803 8834711711945737353673205)
                  ·
                    refine ⟨828254222994912876906863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8834711711945737353673205 828254222994912876906863)
                    ·
                      rfl

theorem cell22_2419529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 5].length) (baseStart_2419529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2419529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2419529 prefixEnd_2419529 := by exact prefixLift 2419529
  have htrace : WordTrace (prefixWord ++ tailWord_2419529) baseStart_2419529 baseEnd_2419529 := by
    simpa [prefixWord, tailWord_2419529, baseEnd_2419529] using wordTrace_append hprefix tailTrace_2419529
  have hstable : (prefixWord ++ tailWord_2419529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419529).length < 2 ^ (prefixWord ++ tailWord_2419529).sum := by decide
  have hdescent : baseEnd_2419529 < baseStart_2419529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419546 : List Nat := [3, 1, 1, 2, 1, 4, 1, 4, 2, 3]
def baseStart_2419546 : Nat := 118140960795 + 2419546 * 2 ^ 59
def prefixEnd_2419546 : Nat := 4983230072969 + 3 ^ 40 * 2419546 * 2
def baseEnd_2419546 : Nat := 828260042442330499231811

theorem tailTrace_2419546 : CollatzResearch.WordTrace tailWord_2419546 prefixEnd_2419546 828260042442330499231811 := by
  unfold tailWord_2419546
  simp only [CollatzResearch.WordTrace]
  refine ⟨22062023123101385600835623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58832061661603694935561661 22062023123101385600835623)
  ·
    refine ⟨33093034684652078401253435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22062023123101385600835623 33093034684652078401253435)
    ·
      refine ⟨49639552026978117601880153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33093034684652078401253435 49639552026978117601880153)
      ·
        refine ⟨37229664020233588201410115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49639552026978117601880153 37229664020233588201410115)
        ·
          refine ⟨55844496030350382302115173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37229664020233588201410115 55844496030350382302115173)
          ·
            refine ⟨10470843005690696681646595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55844496030350382302115173 10470843005690696681646595)
            ·
              refine ⟨15706264508536045022469893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10470843005690696681646595 15706264508536045022469893)
              ·
                refine ⟨2944924595350508441713105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15706264508536045022469893 2944924595350508441713105)
                ·
                  refine ⟨2208693446512881331284829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2944924595350508441713105 2208693446512881331284829)
                  ·
                    refine ⟨828260042442330499231811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2208693446512881331284829 828260042442330499231811)
                    ·
                      rfl

theorem cell22_2419546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4, 2, 3].length) (baseStart_2419546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2419546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2419546 prefixEnd_2419546 := by exact prefixLift 2419546
  have htrace : WordTrace (prefixWord ++ tailWord_2419546) baseStart_2419546 baseEnd_2419546 := by
    simpa [prefixWord, tailWord_2419546, baseEnd_2419546] using wordTrace_append hprefix tailTrace_2419546
  have hstable : (prefixWord ++ tailWord_2419546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419546).length < 2 ^ (prefixWord ++ tailWord_2419546).sum := by decide
  have hdescent : baseEnd_2419546 < baseStart_2419546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419548 : List Nat := [2, 2, 4, 2, 1, 2, 1, 4, 4]
def baseStart_2419548 : Nat := 118140960795 + 2419548 * 2 ^ 59
def prefixEnd_2419548 : Nat := 4983230072969 + 3 ^ 40 * 2419548 * 2
def baseEnd_2419548 : Nat := 276086909027734386893935

theorem tailTrace_2419548 : CollatzResearch.WordTrace tailWord_2419548 prefixEnd_2419548 276086909027734386893935 := by
  unfold tailWord_2419548
  simp only [CollatzResearch.WordTrace]
  refine ⟨44124082719199148372457649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58832110292265531163276865 44124082719199148372457649)
  ·
    refine ⟨33093062039399361279343237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44124082719199148372457649 33093062039399361279343237)
    ·
      refine ⟨6204949132387380239876857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33093062039399361279343237 6204949132387380239876857)
      ·
        refine ⟨4653711849290535179907643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6204949132387380239876857 4653711849290535179907643)
        ·
          refine ⟨6980567773935802769861465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4653711849290535179907643 6980567773935802769861465)
          ·
            refine ⟨5235425830451852077396099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6980567773935802769861465 5235425830451852077396099)
            ·
              refine ⟨7853138745677778116094149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5235425830451852077396099 7853138745677778116094149)
              ·
                refine ⟨1472463514814583396767653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7853138745677778116094149 1472463514814583396767653)
                ·
                  refine ⟨276086909027734386893935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1472463514814583396767653 276086909027734386893935)
                  ·
                    rfl

theorem cell22_2419548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 4, 4].length) (baseStart_2419548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2419548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2419548 prefixEnd_2419548 := by exact prefixLift 2419548
  have htrace : WordTrace (prefixWord ++ tailWord_2419548) baseStart_2419548 baseEnd_2419548 := by
    simpa [prefixWord, tailWord_2419548, baseEnd_2419548] using wordTrace_append hprefix tailTrace_2419548
  have hstable : (prefixWord ++ tailWord_2419548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419548).length < 2 ^ (prefixWord ++ tailWord_2419548).sum := by decide
  have hdescent : baseEnd_2419548 < baseStart_2419548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419559 : List Nat := [1, 1, 5, 1, 2, 2, 3, 7]
def baseStart_2419559 : Nat := 118140960795 + 2419559 * 2 ^ 59
def prefixEnd_2419559 : Nat := 4983230072969 + 3 ^ 40 * 2419559 * 2
def baseEnd_2419559 : Nat := 92029388067555866517419

theorem tailTrace_2419559 : CollatzResearch.WordTrace tailWord_2419559 prefixEnd_2419559 92029388067555866517419 := by
  unfold tailWord_2419559
  simp only [CollatzResearch.WordTrace]
  refine ⟨88248566641358445623565731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58832377760905630415710487 88248566641358445623565731)
  ·
    refine ⟨132372849962037668435348597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88248566641358445623565731 132372849962037668435348597)
    ·
      refine ⟨12409954683941031415813931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 132372849962037668435348597 12409954683941031415813931)
      ·
        refine ⟨18614932025911547123720897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12409954683941031415813931 18614932025911547123720897)
        ·
          refine ⟨13961199019433660342790673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18614932025911547123720897 13961199019433660342790673)
          ·
            refine ⟨10470899264575245257093005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13961199019433660342790673 10470899264575245257093005)
            ·
              refine ⟨3926587224215716971409877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10470899264575245257093005 3926587224215716971409877)
              ·
                refine ⟨92029388067555866517419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3926587224215716971409877 92029388067555866517419)
                ·
                  rfl

theorem cell22_2419559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 7].length) (baseStart_2419559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2419559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2419559 prefixEnd_2419559 := by exact prefixLift 2419559
  have htrace : WordTrace (prefixWord ++ tailWord_2419559) baseStart_2419559 baseEnd_2419559 := by
    simpa [prefixWord, tailWord_2419559, baseEnd_2419559] using wordTrace_append hprefix tailTrace_2419559
  have hstable : (prefixWord ++ tailWord_2419559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419559).length < 2 ^ (prefixWord ++ tailWord_2419559).sum := by decide
  have hdescent : baseEnd_2419559 < baseStart_2419559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419619 : List Nat := [1, 1, 1, 4, 1, 2, 4, 1, 2, 5]
def baseStart_2419619 : Nat := 118140960795 + 2419619 * 2 ^ 59
def prefixEnd_2419619 : Nat := 4983230072969 + 3 ^ 40 * 2419619 * 2
def baseEnd_2419619 : Nat := 828285031834182642156587

theorem tailTrace_2419619 : CollatzResearch.WordTrace tailWord_2419619 prefixEnd_2419619 828285031834182642156587 := by
  unfold tailWord_2419619
  simp only [CollatzResearch.WordTrace]
  refine ⟨88250755021141075870749911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58833836680760717247166607 88250755021141075870749911)
  ·
    refine ⟨132376132531711613806124867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88250755021141075870749911 132376132531711613806124867)
    ·
      refine ⟨198564198797567420709187301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132376132531711613806124867 198564198797567420709187301)
      ·
        refine ⟨37230787274543891382972619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 198564198797567420709187301 37230787274543891382972619)
        ·
          refine ⟨55846180911815837074458929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37230787274543891382972619 55846180911815837074458929)
          ·
            refine ⟨41884635683861877805844197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55846180911815837074458929 41884635683861877805844197)
            ·
              refine ⟨7853369190724102088595787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41884635683861877805844197 7853369190724102088595787)
              ·
                refine ⟨11780053786086153132893681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7853369190724102088595787 11780053786086153132893681)
                ·
                  refine ⟨8835040339564614849670261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11780053786086153132893681 8835040339564614849670261)
                  ·
                    refine ⟨828285031834182642156587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8835040339564614849670261 828285031834182642156587)
                    ·
                      rfl

theorem cell22_2419619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 5].length) (baseStart_2419619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2419619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2419619 prefixEnd_2419619 := by exact prefixLift 2419619
  have htrace : WordTrace (prefixWord ++ tailWord_2419619) baseStart_2419619 baseEnd_2419619 := by
    simpa [prefixWord, tailWord_2419619, baseEnd_2419619] using wordTrace_append hprefix tailTrace_2419619
  have hstable : (prefixWord ++ tailWord_2419619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419619).length < 2 ^ (prefixWord ++ tailWord_2419619).sum := by decide
  have hdescent : baseEnd_2419619 < baseStart_2419619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419743 : List Nat := [1, 1, 2, 4, 1, 4, 1, 2, 3, 3]
def baseStart_2419743 : Nat := 118140960795 + 2419743 * 2 ^ 59
def prefixEnd_2419743 : Nat := 4983230072969 + 3 ^ 40 * 2419743 * 2
def baseEnd_2419743 : Nat := 828327479568287652056207

theorem tailTrace_2419743 : CollatzResearch.WordTrace tailWord_2419743 prefixEnd_2419743 828327479568287652056207 := by
  unfold tailWord_2419743
  simp only [CollatzResearch.WordTrace]
  refine ⟨88255277672691845048263883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58836851781794563365509255 88255277672691845048263883)
  ·
    refine ⟨132382916509037767572395825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88255277672691845048263883 132382916509037767572395825)
    ·
      refine ⟨99287187381778325679296869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132382916509037767572395825 99287187381778325679296869)
      ·
        refine ⟨18616347634083436064868163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99287187381778325679296869 18616347634083436064868163)
        ·
          refine ⟨27924521451125154097302245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18616347634083436064868163 27924521451125154097302245)
          ·
            refine ⟨5235847772085966393244171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27924521451125154097302245 5235847772085966393244171)
            ·
              refine ⟨7853771658128949589866257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5235847772085966393244171 7853771658128949589866257)
              ·
                refine ⟨5890328743596712192399693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7853771658128949589866257 5890328743596712192399693)
                ·
                  refine ⟨2208873278848767072149885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5890328743596712192399693 2208873278848767072149885)
                  ·
                    refine ⟨828327479568287652056207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2208873278848767072149885 828327479568287652056207)
                    ·
                      rfl

theorem cell22_2419743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 3, 3].length) (baseStart_2419743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2419743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2419743 prefixEnd_2419743 := by exact prefixLift 2419743
  have htrace : WordTrace (prefixWord ++ tailWord_2419743) baseStart_2419743 baseEnd_2419743 := by
    simpa [prefixWord, tailWord_2419743, baseEnd_2419743] using wordTrace_append hprefix tailTrace_2419743
  have hstable : (prefixWord ++ tailWord_2419743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419743).length < 2 ^ (prefixWord ++ tailWord_2419743).sum := by decide
  have hdescent : baseEnd_2419743 < baseStart_2419743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419760 : List Nat := [2, 1, 1, 1, 2, 4, 4, 3, 1, 3]
def baseStart_2419760 : Nat := 118140960795 + 2419760 * 2 ^ 59
def prefixEnd_2419760 : Nat := 4983230072969 + 3 ^ 40 * 2419760 * 2
def baseEnd_2419760 : Nat := 828333299015705274381155

theorem tailTrace_2419760 : CollatzResearch.WordTrace tailWord_2419760 prefixEnd_2419760 828333299015705274381155 := by
  unfold tailWord_2419760
  simp only [CollatzResearch.WordTrace]
  refine ⟨44127948856815128475816367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58837265142420171301088489 44127948856815128475816367)
  ·
    refine ⟨66191923285222692713724551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44127948856815128475816367 66191923285222692713724551)
    ·
      refine ⟨99287884927834039070586827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66191923285222692713724551 99287884927834039070586827)
      ·
        refine ⟨148931827391751058605880241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99287884927834039070586827 148931827391751058605880241)
        ·
          refine ⟨111698870543813293954410181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148931827391751058605880241 111698870543813293954410181)
          ·
            refine ⟨20943538226964992616451909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111698870543813293954410181 20943538226964992616451909)
            ·
              refine ⟨3926913417555936115584733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20943538226964992616451909 3926913417555936115584733)
              ·
                refine ⟨1472592531583476043344275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3926913417555936115584733 1472592531583476043344275)
                ·
                  refine ⟨2208888797375214065016413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1472592531583476043344275 2208888797375214065016413)
                  ·
                    refine ⟨828333299015705274381155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2208888797375214065016413 828333299015705274381155)
                    ·
                      rfl

theorem cell22_2419760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 3, 1, 3].length) (baseStart_2419760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2419760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2419760 prefixEnd_2419760 := by exact prefixLift 2419760
  have htrace : WordTrace (prefixWord ++ tailWord_2419760) baseStart_2419760 baseEnd_2419760 := by
    simpa [prefixWord, tailWord_2419760, baseEnd_2419760] using wordTrace_append hprefix tailTrace_2419760
  have hstable : (prefixWord ++ tailWord_2419760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419760).length < 2 ^ (prefixWord ++ tailWord_2419760).sum := by decide
  have hdescent : baseEnd_2419760 < baseStart_2419760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419773 : List Nat := [1, 4, 1, 3, 1, 2, 3, 2, 5]
def baseStart_2419773 : Nat := 118140960795 + 2419773 * 2 ^ 59
def prefixEnd_2419773 : Nat := 4983230072969 + 3 ^ 40 * 2419773 * 2
def baseEnd_2419773 : Nat := 276112583060459191268705

theorem tailTrace_2419773 : CollatzResearch.WordTrace tailWord_2419773 prefixEnd_2419773 276112583060459191268705 := by
  unfold tailWord_2419773
  simp only [CollatzResearch.WordTrace]
  refine ⟨88256371862583160171855973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58837581241722106781237315 88256371862583160171855973)
  ·
    refine ⟨16548069724234342532222995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88256371862583160171855973 16548069724234342532222995)
    ·
      refine ⟨24822104586351513798334493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16548069724234342532222995 24822104586351513798334493)
      ·
        refine ⟨9308289219881817674375435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24822104586351513798334493 9308289219881817674375435)
        ·
          refine ⟨13962433829822726511563153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9308289219881817674375435 13962433829822726511563153)
          ·
            refine ⟨10471825372367044883672365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13962433829822726511563153 10471825372367044883672365)
            ·
              refine ⟨3926934514637641831377137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10471825372367044883672365 3926934514637641831377137)
              ·
                refine ⟨2945200885978231373532853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3926934514637641831377137 2945200885978231373532853)
                ·
                  refine ⟨276112583060459191268705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2945200885978231373532853 276112583060459191268705)
                  ·
                    rfl

theorem cell22_2419773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_2419773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2419773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2419773 prefixEnd_2419773 := by exact prefixLift 2419773
  have htrace : WordTrace (prefixWord ++ tailWord_2419773) baseStart_2419773 baseEnd_2419773 := by
    simpa [prefixWord, tailWord_2419773, baseEnd_2419773] using wordTrace_append hprefix tailTrace_2419773
  have hstable : (prefixWord ++ tailWord_2419773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419773).length < 2 ^ (prefixWord ++ tailWord_2419773).sum := by decide
  have hdescent : baseEnd_2419773 < baseStart_2419773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419786 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 5, 4]
def baseStart_2419786 : Nat := 118140960795 + 2419786 * 2 ^ 59
def prefixEnd_2419786 : Nat := 4983230072969 + 3 ^ 40 * 2419786 * 2
def baseEnd_2419786 : Nat := 828342199347049873231075

theorem tailTrace_2419786 : CollatzResearch.WordTrace tailWord_2419786 prefixEnd_2419786 828342199347049873231075 := by
  unfold tailWord_2419786
  simp only [CollatzResearch.WordTrace]
  refine ⟨22064211502884015848019803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58837897341024042261386141 22064211502884015848019803)
  ·
    refine ⟨33096317254326023772029705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22064211502884015848019803 33096317254326023772029705)
    ·
      refine ⟨24822237940744517829022279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33096317254326023772029705 24822237940744517829022279)
      ·
        refine ⟨37233356911116776743533419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24822237940744517829022279 37233356911116776743533419)
        ·
          refine ⟨55850035366675165115300129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37233356911116776743533419 55850035366675165115300129)
          ·
            refine ⟨41887526525006373836475097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55850035366675165115300129 41887526525006373836475097)
            ·
              refine ⟨31415644893754780377356323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41887526525006373836475097 31415644893754780377356323)
              ·
                refine ⟨47123467340632170566034485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31415644893754780377356323 47123467340632170566034485)
                ·
                  refine ⟨4417825063184265990565733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47123467340632170566034485 4417825063184265990565733)
                  ·
                    refine ⟨828342199347049873231075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4417825063184265990565733 828342199347049873231075)
                    ·
                      rfl

theorem cell22_2419786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_2419786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2419786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2419786 prefixEnd_2419786 := by exact prefixLift 2419786
  have htrace : WordTrace (prefixWord ++ tailWord_2419786) baseStart_2419786 baseEnd_2419786 := by
    simpa [prefixWord, tailWord_2419786, baseEnd_2419786] using wordTrace_append hprefix tailTrace_2419786
  have hstable : (prefixWord ++ tailWord_2419786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419786).length < 2 ^ (prefixWord ++ tailWord_2419786).sum := by decide
  have hdescent : baseEnd_2419786 < baseStart_2419786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419850 : List Nat := [3, 1, 2, 3, 1, 1, 3, 3, 2, 3]
def baseStart_2419850 : Nat := 118140960795 + 2419850 * 2 ^ 59
def prefixEnd_2419850 : Nat := 4983230072969 + 3 ^ 40 * 2419850 * 2
def baseEnd_2419850 : Nat := 828364107854975039630879

theorem tailTrace_2419850 : CollatzResearch.WordTrace tailWord_2419850 prefixEnd_2419850 828364107854975039630879 := by
  unfold tailWord_2419850
  simp only [CollatzResearch.WordTrace]
  refine ⟨22064795070826050580602251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58839453522202801548272669 22064795070826050580602251)
  ·
    refine ⟨33097192606239075870903377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22064795070826050580602251 33097192606239075870903377)
    ·
      refine ⟨24822894454679306903177533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33097192606239075870903377 24822894454679306903177533)
      ·
        refine ⟨9308585420504740088691575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24822894454679306903177533 9308585420504740088691575)
        ·
          refine ⟨13962878130757110133037363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9308585420504740088691575 13962878130757110133037363)
          ·
            refine ⟨20944317196135665199556045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13962878130757110133037363 20944317196135665199556045)
            ·
              refine ⟨7854118948550874449833517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20944317196135665199556045 7854118948550874449833517)
              ·
                refine ⟨2945294605706577918687569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7854118948550874449833517 2945294605706577918687569)
                ·
                  refine ⟨2208970954279933439015677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2945294605706577918687569 2208970954279933439015677)
                  ·
                    refine ⟨828364107854975039630879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2208970954279933439015677 828364107854975039630879)
                    ·
                      rfl

theorem cell22_2419850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3, 2, 3].length) (baseStart_2419850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2419850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2419850 prefixEnd_2419850 := by exact prefixLift 2419850
  have htrace : WordTrace (prefixWord ++ tailWord_2419850) baseStart_2419850 baseEnd_2419850 := by
    simpa [prefixWord, tailWord_2419850, baseEnd_2419850] using wordTrace_append hprefix tailTrace_2419850
  have hstable : (prefixWord ++ tailWord_2419850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419850).length < 2 ^ (prefixWord ++ tailWord_2419850).sum := by decide
  have hdescent : baseEnd_2419850 < baseStart_2419850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419891 : List Nat := [1, 1, 1, 2, 3, 2, 2, 3, 7]
def baseStart_2419891 : Nat := 118140960795 + 2419891 * 2 ^ 59
def prefixEnd_2419891 : Nat := 4983230072969 + 3 ^ 40 * 2419891 * 2
def baseEnd_2419891 : Nat := 276126047664288199785251

theorem tailTrace_2419891 : CollatzResearch.WordTrace tailWord_2419891 prefixEnd_2419891 276126047664288199785251 := by
  unfold tailWord_2419891
  simp only [CollatzResearch.WordTrace]
  refine ⟨88260675676155666324651527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58840450450770444216434351 88260675676155666324651527)
  ·
    refine ⟨132391013514233499486977291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88260675676155666324651527 132391013514233499486977291)
    ·
      refine ⟨198586520271350249230465937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132391013514233499486977291 198586520271350249230465937)
      ·
        refine ⟨148939890203512686922849453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198586520271350249230465937 148939890203512686922849453)
        ·
          refine ⟨55852458826317257596068545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148939890203512686922849453 55852458826317257596068545)
          ·
            refine ⟨41889344119737943197051409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55852458826317257596068545 41889344119737943197051409)
            ·
              refine ⟨31417008089803457397788557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41889344119737943197051409 31417008089803457397788557)
              ·
                refine ⟨11781378033676296524170709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31417008089803457397788557 11781378033676296524170709)
                ·
                  refine ⟨276126047664288199785251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11781378033676296524170709 276126047664288199785251)
                  ·
                    rfl

theorem cell22_2419891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 7].length) (baseStart_2419891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2419891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2419891 prefixEnd_2419891 := by exact prefixLift 2419891
  have htrace : WordTrace (prefixWord ++ tailWord_2419891) baseStart_2419891 baseEnd_2419891 := by
    simpa [prefixWord, tailWord_2419891, baseEnd_2419891] using wordTrace_append hprefix tailTrace_2419891
  have hstable : (prefixWord ++ tailWord_2419891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419891).length < 2 ^ (prefixWord ++ tailWord_2419891).sum := by decide
  have hdescent : baseEnd_2419891 < baseStart_2419891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419972 : List Nat := [2, 3, 2, 2, 2, 2, 2, 2, 1, 4]
def baseStart_2419972 : Nat := 118140960795 + 2419972 * 2 ^ 59
def prefixEnd_2419972 : Nat := 4983230072969 + 3 ^ 40 * 2419972 * 2
def baseEnd_2419972 : Nat := 828405870948207388080505

theorem tailTrace_2419972 : CollatzResearch.WordTrace tailWord_2419972 prefixEnd_2419972 828405870948207388080505 := by
  unfold tailWord_2419972
  simp only [CollatzResearch.WordTrace]
  refine ⟨44131814994431108579175085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58842419992574811438900113 44131814994431108579175085)
  ·
    refine ⟨16549430622911665717190657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44131814994431108579175085 16549430622911665717190657)
    ·
      refine ⟨12412072967183749287892993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16549430622911665717190657 12412072967183749287892993)
      ·
        refine ⟨9309054725387811965919745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12412072967183749287892993 9309054725387811965919745)
        ·
          refine ⟨6981791044040858974439809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9309054725387811965919745 6981791044040858974439809)
          ·
            refine ⟨5236343283030644230829857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6981791044040858974439809 5236343283030644230829857)
            ·
              refine ⟨3927257462272983173122393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5236343283030644230829857 3927257462272983173122393)
              ·
                refine ⟨2945443096704737379841795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3927257462272983173122393 2945443096704737379841795)
                ·
                  refine ⟨4418164645057106069762693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2945443096704737379841795 4418164645057106069762693)
                  ·
                    refine ⟨828405870948207388080505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4418164645057106069762693 828405870948207388080505)
                    ·
                      rfl

theorem cell22_2419972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_2419972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2419972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2419972 prefixEnd_2419972 := by exact prefixLift 2419972
  have htrace : WordTrace (prefixWord ++ tailWord_2419972) baseStart_2419972 baseEnd_2419972 := by
    simpa [prefixWord, tailWord_2419972, baseEnd_2419972] using wordTrace_append hprefix tailTrace_2419972
  have hstable : (prefixWord ++ tailWord_2419972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419972).length < 2 ^ (prefixWord ++ tailWord_2419972).sum := by decide
  have hdescent : baseEnd_2419972 < baseStart_2419972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420019 : List Nat := [1, 1, 1, 2, 5, 4, 2, 1, 2, 3]
def baseStart_2420019 : Nat := 118140960795 + 2420019 * 2 ^ 59
def prefixEnd_2420019 : Nat := 4983230072969 + 3 ^ 40 * 2420019 * 2
def baseEnd_2420019 : Nat := 828421960008714932155361

theorem tailTrace_2420019 : CollatzResearch.WordTrace tailWord_2420019 prefixEnd_2420019 828421960008714932155361 := by
  unfold tailWord_2420019
  simp only [CollatzResearch.WordTrace]
  refine ⟨88265344219691944185311111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58843562813127962790207407 88265344219691944185311111)
  ·
    refine ⟨132398016329537916277966667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88265344219691944185311111 132398016329537916277966667)
    ·
      refine ⟨198597024494306874416950001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132398016329537916277966667 198597024494306874416950001)
      ·
        refine ⟨148947768370730155812712501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198597024494306874416950001 148947768370730155812712501)
        ·
          refine ⟨13963853284755952107441797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 148947768370730155812712501 13963853284755952107441797)
          ·
            refine ⟨2618222490891741020145337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13963853284755952107441797 2618222490891741020145337)
            ·
              refine ⟨1963666868168805765109003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2618222490891741020145337 1963666868168805765109003)
              ·
                refine ⟨2945500302253208647663505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1963666868168805765109003 2945500302253208647663505)
                ·
                  refine ⟨2209125226689906485747629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2945500302253208647663505 2209125226689906485747629)
                  ·
                    refine ⟨828421960008714932155361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2209125226689906485747629 828421960008714932155361)
                    ·
                      rfl

theorem cell22_2420019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 1, 2, 3].length) (baseStart_2420019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2420019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2420019 prefixEnd_2420019 := by exact prefixLift 2420019
  have htrace : WordTrace (prefixWord ++ tailWord_2420019) baseStart_2420019 baseEnd_2420019 := by
    simpa [prefixWord, tailWord_2420019, baseEnd_2420019] using wordTrace_append hprefix tailTrace_2420019
  have hstable : (prefixWord ++ tailWord_2420019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420019).length < 2 ^ (prefixWord ++ tailWord_2420019).sum := by decide
  have hdescent : baseEnd_2420019 < baseStart_2420019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420064 : List Nat := [2, 1, 1, 3, 4, 2, 1, 4, 1, 3]
def baseStart_2420064 : Nat := 118140960795 + 2420064 * 2 ^ 59
def prefixEnd_2420064 : Nat := 4983230072969 + 3 ^ 40 * 2420064 * 2
def baseEnd_2420064 : Nat := 828437364428349814780223

theorem tailTrace_2420064 : CollatzResearch.WordTrace tailWord_2420064 prefixEnd_2420064 828437364428349814780223 := by
  unfold tailWord_2420064
  simp only [CollatzResearch.WordTrace]
  refine ⟨44133492752264458435349623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58844657003019277913799497 44133492752264458435349623)
  ·
    refine ⟨66200239128396687653024435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44133492752264458435349623 66200239128396687653024435)
    ·
      refine ⟨99300358692595031479536653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66200239128396687653024435 99300358692595031479536653)
      ·
        refine ⟨37237634509723136804826245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99300358692595031479536653 37237634509723136804826245)
        ·
          refine ⟨6982056470573088150904921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37237634509723136804826245 6982056470573088150904921)
          ·
            refine ⟨5236542352929816113178691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6982056470573088150904921 5236542352929816113178691)
            ·
              refine ⟨7854813529394724169768037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5236542352929816113178691 7854813529394724169768037)
              ·
                refine ⟨1472777536761510781831507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7854813529394724169768037 1472777536761510781831507)
                ·
                  refine ⟨2209166305142266172747261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1472777536761510781831507 2209166305142266172747261)
                  ·
                    refine ⟨828437364428349814780223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2209166305142266172747261 828437364428349814780223)
                    ·
                      rfl

theorem cell22_2420064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 4, 1, 3].length) (baseStart_2420064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2420064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2420064 prefixEnd_2420064 := by exact prefixLift 2420064
  have htrace : WordTrace (prefixWord ++ tailWord_2420064) baseStart_2420064 baseEnd_2420064 := by
    simpa [prefixWord, tailWord_2420064, baseEnd_2420064] using wordTrace_append hprefix tailTrace_2420064
  have hstable : (prefixWord ++ tailWord_2420064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420064).length < 2 ^ (prefixWord ++ tailWord_2420064).sum := by decide
  have hdescent : baseEnd_2420064 < baseStart_2420064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420098 : List Nat := [3, 4, 2, 1, 1, 2, 2, 3, 1, 3]
def baseStart_2420098 : Nat := 118140960795 + 2420098 * 2 ^ 59
def prefixEnd_2420098 : Nat := 4983230072969 + 3 ^ 40 * 2420098 * 2
def baseEnd_2420098 : Nat := 828449003323185059430119

theorem tailTrace_2420098 : CollatzResearch.WordTrace tailWord_2420098 prefixEnd_2420098 828449003323185059430119 := by
  unfold tailWord_2420098
  simp only [CollatzResearch.WordTrace]
  refine ⟨22067056396601435169359237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58845483724270493784957965 22067056396601435169359237)
  ·
    refine ⟨4137573074362769094254857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22067056396601435169359237 4137573074362769094254857)
    ·
      refine ⟨3103179805772076820691143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4137573074362769094254857 3103179805772076820691143)
      ·
        refine ⟨4654769708658115231036715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3103179805772076820691143 4654769708658115231036715)
        ·
          refine ⟨6982154562987172846555073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4654769708658115231036715 6982154562987172846555073)
          ·
            refine ⟨5236615922240379634916305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6982154562987172846555073 5236615922240379634916305)
            ·
              refine ⟨3927461941680284726187229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5236615922240379634916305 3927461941680284726187229)
              ·
                refine ⟨1472798228130106772320211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3927461941680284726187229 1472798228130106772320211)
                ·
                  refine ⟨2209197342195160158480317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1472798228130106772320211 2209197342195160158480317)
                  ·
                    refine ⟨828449003323185059430119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2209197342195160158480317 828449003323185059430119)
                    ·
                      rfl

theorem cell22_2420098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_2420098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2420098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2420098 prefixEnd_2420098 := by exact prefixLift 2420098
  have htrace : WordTrace (prefixWord ++ tailWord_2420098) baseStart_2420098 baseEnd_2420098 := by
    simpa [prefixWord, tailWord_2420098, baseEnd_2420098] using wordTrace_append hprefix tailTrace_2420098
  have hstable : (prefixWord ++ tailWord_2420098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420098).length < 2 ^ (prefixWord ++ tailWord_2420098).sum := by decide
  have hdescent : baseEnd_2420098 < baseStart_2420098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420122 : List Nat := [3, 1, 1, 4, 1, 1, 1, 6, 4]
def baseStart_2420122 : Nat := 118140960795 + 2420122 * 2 ^ 59
def prefixEnd_2420122 : Nat := 4983230072969 + 3 ^ 40 * 2420122 * 2
def baseEnd_2420122 : Nat := 276152406337885665610015

theorem tailTrace_2420122 : CollatzResearch.WordTrace tailWord_2420122 prefixEnd_2420122 276152406337885665610015 := by
  unfold tailWord_2420122
  simp only [CollatzResearch.WordTrace]
  refine ⟨22067275234579698194077655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58846067292212528517540413 22067275234579698194077655)
  ·
    refine ⟨33100912851869547291116483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22067275234579698194077655 33100912851869547291116483)
    ·
      refine ⟨49651369277804320936674725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33100912851869547291116483 49651369277804320936674725)
      ·
        refine ⟨9309631739588310175626511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49651369277804320936674725 9309631739588310175626511)
        ·
          refine ⟨13964447609382465263439767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9309631739588310175626511 13964447609382465263439767)
          ·
            refine ⟨20946671414073697895159651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13964447609382465263439767 20946671414073697895159651)
            ·
              refine ⟨31420007121110546842739477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20946671414073697895159651 31420007121110546842739477)
              ·
                refine ⟨1472812833802056883253413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31420007121110546842739477 1472812833802056883253413)
                ·
                  refine ⟨276152406337885665610015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1472812833802056883253413 276152406337885665610015)
                  ·
                    rfl

theorem cell22_2420122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 6, 4].length) (baseStart_2420122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2420122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2420122 prefixEnd_2420122 := by exact prefixLift 2420122
  have htrace : WordTrace (prefixWord ++ tailWord_2420122) baseStart_2420122 baseEnd_2420122 := by
    simpa [prefixWord, tailWord_2420122, baseEnd_2420122] using wordTrace_append hprefix tailTrace_2420122
  have hstable : (prefixWord ++ tailWord_2420122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420122).length < 2 ^ (prefixWord ++ tailWord_2420122).sum := by decide
  have hdescent : baseEnd_2420122 < baseStart_2420122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420135 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 3, 6]
def baseStart_2420135 : Nat := 118140960795 + 2420135 * 2 ^ 59
def prefixEnd_2420135 : Nat := 4983230072969 + 3 ^ 40 * 2420135 * 2
def baseEnd_2420135 : Nat := 828461669179329296255005

theorem tailTrace_2420135 : CollatzResearch.WordTrace tailWord_2420135 prefixEnd_2420135 828461669179329296255005 := by
  unfold tailWord_2420135
  simp only [CollatzResearch.WordTrace]
  refine ⟨88269575087271695996533859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58846383391514463997689239 88269575087271695996533859)
  ·
    refine ⟨132404362630907543994800789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88269575087271695996533859 132404362630907543994800789)
    ·
      refine ⟨6206454498323791124756287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 132404362630907543994800789 6206454498323791124756287)
      ·
        refine ⟨9309681747485686687134431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6206454498323791124756287 9309681747485686687134431)
        ·
          refine ⟨13964522621228530030701647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9309681747485686687134431 13964522621228530030701647)
          ·
            refine ⟨20946783931842795046052471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13964522621228530030701647 20946783931842795046052471)
            ·
              refine ⟨31420175897764192569078707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20946783931842795046052471 31420175897764192569078707)
              ·
                refine ⟨47130263846646288853618061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31420175897764192569078707 47130263846646288853618061)
                ·
                  refine ⟨17673848942492358320106773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47130263846646288853618061 17673848942492358320106773)
                  ·
                    refine ⟨828461669179329296255005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17673848942492358320106773 828461669179329296255005)
                    ·
                      rfl

theorem cell22_2420135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_2420135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2420135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2420135 prefixEnd_2420135 := by exact prefixLift 2420135
  have htrace : WordTrace (prefixWord ++ tailWord_2420135) baseStart_2420135 baseEnd_2420135 := by
    simpa [prefixWord, tailWord_2420135, baseEnd_2420135] using wordTrace_append hprefix tailTrace_2420135
  have hstable : (prefixWord ++ tailWord_2420135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420135).length < 2 ^ (prefixWord ++ tailWord_2420135).sum := by decide
  have hdescent : baseEnd_2420135 < baseStart_2420135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420156 : List Nat := [2, 2, 2, 4, 2, 2, 1, 3, 4]
def baseStart_2420156 : Nat := 118140960795 + 2420156 * 2 ^ 59
def prefixEnd_2420156 : Nat := 4983230072969 + 3 ^ 40 * 2420156 * 2
def baseEnd_2420156 : Nat := 276156285969497413826647

theorem tailTrace_2420156 : CollatzResearch.WordTrace tailWord_2420156 prefixEnd_2420156 276156285969497413826647 := by
  unfold tailWord_2420156
  simp only [CollatzResearch.WordTrace]
  refine ⟨44135170510097808291524161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58846894013463744388698881 44135170510097808291524161)
  ·
    refine ⟨33101377882573356218643121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44135170510097808291524161 33101377882573356218643121)
    ·
      refine ⟨24826033411930017163982341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33101377882573356218643121 24826033411930017163982341)
      ·
        refine ⟨4654881264736878218246689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24826033411930017163982341 4654881264736878218246689)
        ·
          refine ⟨3491160948552658663685017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4654881264736878218246689 3491160948552658663685017)
          ·
            refine ⟨2618370711414493997763763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3491160948552658663685017 2618370711414493997763763)
            ·
              refine ⟨3927556067121740996645645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2618370711414493997763763 3927556067121740996645645)
              ·
                refine ⟨1472833525170652873742117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3927556067121740996645645 1472833525170652873742117)
                ·
                  refine ⟨276156285969497413826647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1472833525170652873742117 276156285969497413826647)
                  ·
                    rfl

theorem cell22_2420156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 3, 4].length) (baseStart_2420156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2420156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2420156 prefixEnd_2420156 := by exact prefixLift 2420156
  have htrace : WordTrace (prefixWord ++ tailWord_2420156) baseStart_2420156 baseEnd_2420156 := by
    simpa [prefixWord, tailWord_2420156, baseEnd_2420156] using wordTrace_append hprefix tailTrace_2420156
  have hstable : (prefixWord ++ tailWord_2420156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420156).length < 2 ^ (prefixWord ++ tailWord_2420156).sum := by decide
  have hdescent : baseEnd_2420156 < baseStart_2420156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420257 : List Nat := [1, 2, 3, 2, 2, 3, 1, 2, 6]
def baseStart_2420257 : Nat := 118140960795 + 2420257 * 2 ^ 59
def prefixEnd_2420257 : Nat := 4983230072969 + 3 ^ 40 * 2420257 * 2
def baseEnd_2420257 : Nat := 276167810757520548234877

theorem tailTrace_2420257 : CollatzResearch.WordTrace tailWord_2420257 prefixEnd_2420257 276167810757520548234877 := by
  unfold tailWord_2420257
  simp only [CollatzResearch.WordTrace]
  refine ⟨88274024792829710832475025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58849349861886473888316683 88274024792829710832475025)
  ·
    refine ⟨66205518594622283124356269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88274024792829710832475025 66205518594622283124356269)
    ·
      refine ⟨24827069472983356171633601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66205518594622283124356269 24827069472983356171633601)
      ·
        refine ⟨18620302104737517128725201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24827069472983356171633601 18620302104737517128725201)
        ·
          refine ⟨13965226578553137846543901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18620302104737517128725201 13965226578553137846543901)
          ·
            refine ⟨5236959966957426692453963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13965226578553137846543901 5236959966957426692453963)
            ·
              refine ⟨7855439950436140038680945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5236959966957426692453963 7855439950436140038680945)
              ·
                refine ⟨5891579962827105029010709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7855439950436140038680945 5891579962827105029010709)
                ·
                  refine ⟨276167810757520548234877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5891579962827105029010709 276167810757520548234877)
                  ·
                    rfl

theorem cell22_2420257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 6].length) (baseStart_2420257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2420257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2420257 prefixEnd_2420257 := by exact prefixLift 2420257
  have htrace : WordTrace (prefixWord ++ tailWord_2420257) baseStart_2420257 baseEnd_2420257 := by
    simpa [prefixWord, tailWord_2420257, baseEnd_2420257] using wordTrace_append hprefix tailTrace_2420257
  have hstable : (prefixWord ++ tailWord_2420257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420257).length < 2 ^ (prefixWord ++ tailWord_2420257).sum := by decide
  have hdescent : baseEnd_2420257 < baseStart_2420257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420272 : List Nat := [2, 1, 1, 1, 2, 3, 1, 4, 4, 3]
def baseStart_2420272 : Nat := 118140960795 + 2420272 * 2 ^ 59
def prefixEnd_2420272 : Nat := 4983230072969 + 3 ^ 40 * 2420272 * 2
def baseEnd_2420272 : Nat := 828508567079106605579585

theorem tailTrace_2420272 : CollatzResearch.WordTrace tailWord_2420272 prefixEnd_2420272 828508567079106605579585 := by
  unfold tailWord_2420272
  simp only [CollatzResearch.WordTrace]
  refine ⟨44137285943887684197135535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58849714591850245596180713 44137285943887684197135535)
  ·
    refine ⟨66205928915831526295703303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44137285943887684197135535 66205928915831526295703303)
    ·
      refine ⟨99308893373747289443554955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66205928915831526295703303 99308893373747289443554955)
      ·
        refine ⟨148963340060620934165332433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99308893373747289443554955 148963340060620934165332433)
        ·
          refine ⟨111722505045465700623999325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148963340060620934165332433 111722505045465700623999325)
          ·
            refine ⟨41895939392049637733999747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111722505045465700623999325 41895939392049637733999747)
            ·
              refine ⟨62843909088074456600999621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41895939392049637733999747 62843909088074456600999621)
              ·
                refine ⟨11783232954013960612687429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62843909088074456600999621 11783232954013960612687429)
                ·
                  refine ⟨2209356178877617614878893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11783232954013960612687429 2209356178877617614878893)
                  ·
                    refine ⟨828508567079106605579585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2209356178877617614878893 828508567079106605579585)
                    ·
                      rfl

theorem cell22_2420272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 4, 3].length) (baseStart_2420272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2420272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2420272 prefixEnd_2420272 := by exact prefixLift 2420272
  have htrace : WordTrace (prefixWord ++ tailWord_2420272) baseStart_2420272 baseEnd_2420272 := by
    simpa [prefixWord, tailWord_2420272, baseEnd_2420272] using wordTrace_append hprefix tailTrace_2420272
  have hstable : (prefixWord ++ tailWord_2420272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420272).length < 2 ^ (prefixWord ++ tailWord_2420272).sum := by decide
  have hdescent : baseEnd_2420272 < baseStart_2420272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420289 : List Nat := [1, 2, 5, 1, 1, 1, 3, 1, 4, 3]
def baseStart_2420289 : Nat := 118140960795 + 2420289 * 2 ^ 59
def prefixEnd_2420289 : Nat := 4983230072969 + 3 ^ 40 * 2420289 * 2
def baseEnd_2420289 : Nat := 828514386526524227904533

theorem tailTrace_2420289 : CollatzResearch.WordTrace tailWord_2420289 prefixEnd_2420289 828514386526524227904533 := by
  unfold tailWord_2420289
  simp only [CollatzResearch.WordTrace]
  refine ⟨88275191928713780297639921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58850127952475853531759947 88275191928713780297639921)
  ·
    refine ⟨66206393946535335223229941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88275191928713780297639921 66206393946535335223229941)
    ·
      refine ⟨6206849432487687677177807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66206393946535335223229941 6206849432487687677177807)
      ·
        refine ⟨9310274148731531515766711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6206849432487687677177807 9310274148731531515766711)
        ·
          refine ⟨13965411223097297273650067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9310274148731531515766711 13965411223097297273650067)
          ·
            refine ⟨20948116834645945910475101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13965411223097297273650067 20948116834645945910475101)
            ·
              refine ⟨7855543812992229716428163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20948116834645945910475101 7855543812992229716428163)
              ·
                refine ⟨11783315719488344574642245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7855543812992229716428163 11783315719488344574642245)
                ·
                  refine ⟨2209371697404064607745421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11783315719488344574642245 2209371697404064607745421)
                  ·
                    refine ⟨828514386526524227904533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2209371697404064607745421 828514386526524227904533)
                    ·
                      rfl

theorem cell22_2420289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_2420289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2420289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2420289 prefixEnd_2420289 := by exact prefixLift 2420289
  have htrace : WordTrace (prefixWord ++ tailWord_2420289) baseStart_2420289 baseEnd_2420289 := by
    simpa [prefixWord, tailWord_2420289, baseEnd_2420289] using wordTrace_append hprefix tailTrace_2420289
  have hstable : (prefixWord ++ tailWord_2420289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420289).length < 2 ^ (prefixWord ++ tailWord_2420289).sum := by decide
  have hdescent : baseEnd_2420289 < baseStart_2420289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420310 : List Nat := [5, 2, 2, 2, 1, 1, 2, 2, 1, 4]
def baseStart_2420310 : Nat := 118140960795 + 2420310 * 2 ^ 59
def prefixEnd_2420310 : Nat := 4983230072969 + 3 ^ 40 * 2420310 * 2
def baseEnd_2420310 : Nat := 828521575255687173129469

theorem tailTrace_2420310 : CollatzResearch.WordTrace tailWord_2420310 prefixEnd_2420310 828521575255687173129469 := by
  unfold tailWord_2420310
  simp only [CollatzResearch.WordTrace]
  refine ⟨5517247366352356305259649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58850638574425133922769589 5517247366352356305259649)
  ·
    refine ⟨4137935524764267228944737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5517247366352356305259649 4137935524764267228944737)
    ·
      refine ⟨3103451643573200421708553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4137935524764267228944737 3103451643573200421708553)
      ·
        refine ⟨2327588732679900316281415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3103451643573200421708553 2327588732679900316281415)
        ·
          refine ⟨3491383099019850474422123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2327588732679900316281415 3491383099019850474422123)
          ·
            refine ⟨5237074648529775711633185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3491383099019850474422123 5237074648529775711633185)
            ·
              refine ⟨3927805986397331783724889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5237074648529775711633185 3927805986397331783724889)
              ·
                refine ⟨2945854489797998837793667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3927805986397331783724889 2945854489797998837793667)
                ·
                  refine ⟨4418781734696998256690501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2945854489797998837793667 4418781734696998256690501)
                  ·
                    refine ⟨828521575255687173129469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4418781734696998256690501 828521575255687173129469)
                    ·
                      rfl

theorem cell22_2420310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_2420310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2420310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2420310 prefixEnd_2420310 := by exact prefixLift 2420310
  have htrace : WordTrace (prefixWord ++ tailWord_2420310) baseStart_2420310 baseEnd_2420310 := by
    simpa [prefixWord, tailWord_2420310, baseEnd_2420310] using wordTrace_append hprefix tailTrace_2420310
  have hstable : (prefixWord ++ tailWord_2420310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420310).length < 2 ^ (prefixWord ++ tailWord_2420310).sum := by decide
  have hdescent : baseEnd_2420310 < baseStart_2420310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420347 : List Nat := [1, 1, 1, 1, 1, 4, 4, 4, 5]
def baseStart_2420347 : Nat := 118140960795 + 2420347 * 2 ^ 59
def prefixEnd_2420347 : Nat := 4983230072969 + 3 ^ 40 * 2420347 * 2
def baseEnd_2420347 : Nat := 276178080370610469984785

theorem tailTrace_2420347 : CollatzResearch.WordTrace tailWord_2420347 prefixEnd_2420347 276178080370610469984785 := by
  unfold tailWord_2420347
  simp only [CollatzResearch.WordTrace]
  refine ⟨88277307362503656203251295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58851538241669104135500863 88277307362503656203251295)
  ·
    refine ⟨132415961043755484304876943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88277307362503656203251295 132415961043755484304876943)
    ·
      refine ⟨198623941565633226457315415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132415961043755484304876943 198623941565633226457315415)
      ·
        refine ⟨297935912348449839685973123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198623941565633226457315415 297935912348449839685973123)
        ·
          refine ⟨446903868522674759528959685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297935912348449839685973123 446903868522674759528959685)
          ·
            refine ⟨83794475348001517411679941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 446903868522674759528959685 83794475348001517411679941)
            ·
              refine ⟨15711464127750284514689989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83794475348001517411679941 15711464127750284514689989)
              ·
                refine ⟨2945899523953178346504373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15711464127750284514689989 2945899523953178346504373)
                ·
                  refine ⟨276178080370610469984785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2945899523953178346504373 276178080370610469984785)
                  ·
                    rfl

theorem cell22_2420347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 5].length) (baseStart_2420347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2420347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2420347 prefixEnd_2420347 := by exact prefixLift 2420347
  have htrace : WordTrace (prefixWord ++ tailWord_2420347) baseStart_2420347 baseEnd_2420347 := by
    simpa [prefixWord, tailWord_2420347, baseEnd_2420347] using wordTrace_append hprefix tailTrace_2420347
  have hstable : (prefixWord ++ tailWord_2420347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420347).length < 2 ^ (prefixWord ++ tailWord_2420347).sum := by decide
  have hdescent : baseEnd_2420347 < baseStart_2420347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420398 : List Nat := [4, 1, 4, 1, 2, 1, 2, 2, 5]
def baseStart_2420398 : Nat := 118140960795 + 2420398 * 2 ^ 59
def prefixEnd_2420398 : Nat := 4983230072969 + 3 ^ 40 * 2420398 * 2
def baseEnd_2420398 : Nat := 276183899818028092309733

theorem tailTrace_2420398 : CollatzResearch.WordTrace tailWord_2420398 prefixEnd_2420398 276183899818028092309733 := by
  unfold tailWord_2420398
  simp only [CollatzResearch.WordTrace]
  refine ⟨11034895935664861489169731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58852778323545927942238565 11034895935664861489169731)
  ·
    refine ⟨16552343903497292233754597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11034895935664861489169731 16552343903497292233754597)
    ·
      refine ⟨3103564481905742293828987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16552343903497292233754597 3103564481905742293828987)
      ·
        refine ⟨4655346722858613440743481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3103564481905742293828987 4655346722858613440743481)
        ·
          refine ⟨3491510042143960080557611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4655346722858613440743481 3491510042143960080557611)
          ·
            refine ⟨5237265063215940120836417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3491510042143960080557611 5237265063215940120836417)
            ·
              refine ⟨3927948797411955090627313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5237265063215940120836417 3927948797411955090627313)
              ·
                refine ⟨2945961598058966317970485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3927948797411955090627313 2945961598058966317970485)
                ·
                  refine ⟨276183899818028092309733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2945961598058966317970485 276183899818028092309733)
                  ·
                    rfl

theorem cell22_2420398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_2420398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2420398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2420398 prefixEnd_2420398 := by exact prefixLift 2420398
  have htrace : WordTrace (prefixWord ++ tailWord_2420398) baseStart_2420398 baseEnd_2420398 := by
    simpa [prefixWord, tailWord_2420398, baseEnd_2420398] using wordTrace_append hprefix tailTrace_2420398
  have hstable : (prefixWord ++ tailWord_2420398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420398).length < 2 ^ (prefixWord ++ tailWord_2420398).sum := by decide
  have hdescent : baseEnd_2420398 < baseStart_2420398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420424 : List Nat := [2, 1, 3, 1, 2, 2, 4, 1, 1, 5]
def baseStart_2420424 : Nat := 118140960795 + 2420424 * 2 ^ 59
def prefixEnd_2420424 : Nat := 4983230072969 + 3 ^ 40 * 2420424 * 2
def baseEnd_2420424 : Nat := 828560599785428875779119

theorem tailTrace_2420424 : CollatzResearch.WordTrace tailWord_2420424 prefixEnd_2420424 828560599785428875779119 := by
  unfold tailWord_2420424
  simp only [CollatzResearch.WordTrace]
  refine ⟨44140057891612349176902163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58853410522149798902536217 44140057891612349176902163)
  ·
    refine ⟨66210086837418523765353245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44140057891612349176902163 66210086837418523765353245)
    ·
      refine ⟨24828782564031946412007467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66210086837418523765353245 24828782564031946412007467)
      ·
        refine ⟨37243173846047919618011201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24828782564031946412007467 37243173846047919618011201)
        ·
          refine ⟨27932380384535939713508401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37243173846047919618011201 27932380384535939713508401)
          ·
            refine ⟨20949285288401954785131301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27932380384535939713508401 20949285288401954785131301)
            ·
              refine ⟨3927990991575366522212119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20949285288401954785131301 3927990991575366522212119)
              ·
                refine ⟨5891986487363049783318179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3927990991575366522212119 5891986487363049783318179)
                ·
                  refine ⟨8837979731044574674977269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5891986487363049783318179 8837979731044574674977269)
                  ·
                    refine ⟨828560599785428875779119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8837979731044574674977269 828560599785428875779119)
                    ·
                      rfl

theorem cell22_2420424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_2420424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2420424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2420424 prefixEnd_2420424 := by exact prefixLift 2420424
  have htrace : WordTrace (prefixWord ++ tailWord_2420424) baseStart_2420424 baseEnd_2420424 := by
    simpa [prefixWord, tailWord_2420424, baseEnd_2420424] using wordTrace_append hprefix tailTrace_2420424
  have hstable : (prefixWord ++ tailWord_2420424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420424).length < 2 ^ (prefixWord ++ tailWord_2420424).sum := by decide
  have hdescent : baseEnd_2420424 < baseStart_2420424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420467 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 1, 8]
def baseStart_2420467 : Nat := 118140960795 + 2420467 * 2 ^ 59
def prefixEnd_2420467 : Nat := 4983230072969 + 3 ^ 40 * 2420467 * 2
def baseEnd_2420467 : Nat := 828575319564191096953987

theorem tailTrace_2420467 : CollatzResearch.WordTrace tailWord_2420467 prefixEnd_2420467 828575319564191096953987 := by
  unfold tailWord_2420467
  simp only [CollatzResearch.WordTrace]
  refine ⟨88281684122068916697619655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58854456081379277798413103 88281684122068916697619655)
  ·
    refine ⟨132422526183103375046429483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88281684122068916697619655 132422526183103375046429483)
    ·
      refine ⟨198633789274655062569644225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132422526183103375046429483 198633789274655062569644225)
      ·
        refine ⟨148975341955991296927233169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198633789274655062569644225 148975341955991296927233169)
        ·
          refine ⟨111731506466993472695424877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148975341955991296927233169 111731506466993472695424877)
          ·
            refine ⟨41899314925122552260784329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111731506466993472695424877 41899314925122552260784329)
            ·
              refine ⟨31424486193841914195588247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41899314925122552260784329 31424486193841914195588247)
              ·
                refine ⟨47136729290762871293382371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31424486193841914195588247 47136729290762871293382371)
                ·
                  refine ⟨70705093936144306940073557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47136729290762871293382371 70705093936144306940073557)
                  ·
                    refine ⟨828575319564191096953987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 70705093936144306940073557 828575319564191096953987)
                    ·
                      rfl

theorem cell22_2420467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 8].length) (baseStart_2420467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2420467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2420467 prefixEnd_2420467 := by exact prefixLift 2420467
  have htrace : WordTrace (prefixWord ++ tailWord_2420467) baseStart_2420467 baseEnd_2420467 := by
    simpa [prefixWord, tailWord_2420467, baseEnd_2420467] using wordTrace_append hprefix tailTrace_2420467
  have hstable : (prefixWord ++ tailWord_2420467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420467).length < 2 ^ (prefixWord ++ tailWord_2420467).sum := by decide
  have hdescent : baseEnd_2420467 < baseStart_2420467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420649 : List Nat := [1, 2, 1, 1, 1, 1, 4, 3, 1, 7]
def baseStart_2420649 : Nat := 118140960795 + 2420649 * 2 ^ 59
def prefixEnd_2420649 : Nat := 4983230072969 + 3 ^ 40 * 2420649 * 2
def baseEnd_2420649 : Nat := 828637621883603288903429

theorem tailTrace_2420649 : CollatzResearch.WordTrace tailWord_2420649 prefixEnd_2420649 828637621883603288903429 := by
  unfold tailWord_2420649
  simp only [CollatzResearch.WordTrace]
  refine ⟨88288322207409561780745001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58858881471606374520496667 88288322207409561780745001)
  ·
    refine ⟨66216241655557171335558751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88288322207409561780745001 66216241655557171335558751)
    ·
      refine ⟨99324362483335757003338127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66216241655557171335558751 99324362483335757003338127)
      ·
        refine ⟨148986543725003635505007191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99324362483335757003338127 148986543725003635505007191)
        ·
          refine ⟨223479815587505453257510787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148986543725003635505007191 223479815587505453257510787)
          ·
            refine ⟨335219723381258179886266181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223479815587505453257510787 335219723381258179886266181)
            ·
              refine ⟨62853698133985908728674909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 335219723381258179886266181 62853698133985908728674909)
              ·
                refine ⟨23570136800244715773253091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62853698133985908728674909 23570136800244715773253091)
                ·
                  refine ⟨35355205200367073659879637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23570136800244715773253091 35355205200367073659879637)
                  ·
                    refine ⟨828637621883603288903429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35355205200367073659879637 828637621883603288903429)
                    ·
                      rfl

theorem cell22_2420649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 7].length) (baseStart_2420649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2420649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2420649 prefixEnd_2420649 := by exact prefixLift 2420649
  have htrace : WordTrace (prefixWord ++ tailWord_2420649) baseStart_2420649 baseEnd_2420649 := by
    simpa [prefixWord, tailWord_2420649, baseEnd_2420649] using wordTrace_append hprefix tailTrace_2420649
  have hstable : (prefixWord ++ tailWord_2420649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420649).length < 2 ^ (prefixWord ++ tailWord_2420649).sum := by decide
  have hdescent : baseEnd_2420649 < baseStart_2420649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420743 : List Nat := [1, 1, 4, 3, 1, 2, 2, 2, 2, 4]
def baseStart_2420743 : Nat := 118140960795 + 2420743 * 2 ^ 59
def prefixEnd_2420743 : Nat := 4983230072969 + 3 ^ 40 * 2420743 * 2
def baseEnd_2420743 : Nat := 828669800004618377053141

theorem tailTrace_2420743 : CollatzResearch.WordTrace tailWord_2420743 prefixEnd_2420743 828669800004618377053141 := by
  unfold tailWord_2420743
  simp only [CollatzResearch.WordTrace]
  refine ⟨88291750669069015834666883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58861167112712677223111255 88291750669069015834666883)
  ·
    refine ⟨132437626003603523752000325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88291750669069015834666883 132437626003603523752000325)
    ·
      refine ⟨24832054875675660703500061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132437626003603523752000325 24832054875675660703500061)
      ·
        refine ⟨9312020578378372763812523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24832054875675660703500061 9312020578378372763812523)
        ·
          refine ⟨13968030867567559145718785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9312020578378372763812523 13968030867567559145718785)
          ·
            refine ⟨10476023150675669359289089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13968030867567559145718785 10476023150675669359289089)
            ·
              refine ⟨7857017363006752019466817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10476023150675669359289089 7857017363006752019466817)
              ·
                refine ⟨5892763022255064014600113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7857017363006752019466817 5892763022255064014600113)
                ·
                  refine ⟨4419572266691298010950085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5892763022255064014600113 4419572266691298010950085)
                  ·
                    refine ⟨828669800004618377053141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4419572266691298010950085 828669800004618377053141)
                    ·
                      rfl

theorem cell22_2420743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_2420743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2420743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2420743 prefixEnd_2420743 := by exact prefixLift 2420743
  have htrace : WordTrace (prefixWord ++ tailWord_2420743) baseStart_2420743 baseEnd_2420743 := by
    simpa [prefixWord, tailWord_2420743, baseEnd_2420743] using wordTrace_append hprefix tailTrace_2420743
  have hstable : (prefixWord ++ tailWord_2420743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420743).length < 2 ^ (prefixWord ++ tailWord_2420743).sum := by decide
  have hdescent : baseEnd_2420743 < baseStart_2420743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420771 : List Nat := [1, 1, 1, 4, 3, 1, 1, 2, 2, 6]
def baseStart_2420771 : Nat := 118140960795 + 2420771 * 2 ^ 59
def prefixEnd_2420771 : Nat := 4983230072969 + 3 ^ 40 * 2420771 * 2
def baseEnd_2420771 : Nat := 828679384976835637353055

theorem tailTrace_2420771 : CollatzResearch.WordTrace tailWord_2420771 prefixEnd_2420771 828679384976835637353055 := by
  unfold tailWord_2420771
  simp only [CollatzResearch.WordTrace]
  refine ⟨88292771912967576616686167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58861847941978384411124111 88292771912967576616686167)
  ·
    refine ⟨132439157869451364925029251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88292771912967576616686167 132439157869451364925029251)
    ·
      refine ⟨198658736804177047387543877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132439157869451364925029251 198658736804177047387543877)
      ·
        refine ⟨37248513150783196385164477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 198658736804177047387543877 37248513150783196385164477)
        ·
          refine ⟨13968192431543698644436679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37248513150783196385164477 13968192431543698644436679)
          ·
            refine ⟨20952288647315547966655019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13968192431543698644436679 20952288647315547966655019)
            ·
              refine ⟨31428432970973321949982529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20952288647315547966655019 31428432970973321949982529)
              ·
                refine ⟨23571324728229991462486897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31428432970973321949982529 23571324728229991462486897)
                ·
                  refine ⟨17678493546172493596865173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23571324728229991462486897 17678493546172493596865173)
                  ·
                    refine ⟨828679384976835637353055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17678493546172493596865173 828679384976835637353055)
                    ·
                      rfl

theorem cell22_2420771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 6].length) (baseStart_2420771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2420771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2420771 prefixEnd_2420771 := by exact prefixLift 2420771
  have htrace : WordTrace (prefixWord ++ tailWord_2420771) baseStart_2420771 baseEnd_2420771 := by
    simpa [prefixWord, tailWord_2420771, baseEnd_2420771] using wordTrace_append hprefix tailTrace_2420771
  have hstable : (prefixWord ++ tailWord_2420771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420771).length < 2 ^ (prefixWord ++ tailWord_2420771).sum := by decide
  have hdescent : baseEnd_2420771 < baseStart_2420771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420773 : List Nat := [1, 3, 1, 2, 2, 3, 1, 1, 5, 3]
def baseStart_2420773 : Nat := 118140960795 + 2420773 * 2 ^ 59
def prefixEnd_2420773 : Nat := 4983230072969 + 3 ^ 40 * 2420773 * 2
def baseEnd_2420773 : Nat := 828680069617708298803049

theorem tailTrace_2420773 : CollatzResearch.WordTrace tailWord_2420773 prefixEnd_2420773 828680069617708298803049 := by
  unfold tailWord_2420773
  simp only [CollatzResearch.WordTrace]
  refine ⟨88292844858960330958258973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58861896572640220638839315 88292844858960330958258973)
  ·
    refine ⟨33109816822110124109347115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88292844858960330958258973 33109816822110124109347115)
    ·
      refine ⟨49664725233165186164020673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33109816822110124109347115 49664725233165186164020673)
      ·
        refine ⟨37248543924873889623015505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49664725233165186164020673 37248543924873889623015505)
        ·
          refine ⟨27936407943655417217261629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37248543924873889623015505 27936407943655417217261629)
          ·
            refine ⟨10476152978870781456473111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27936407943655417217261629 10476152978870781456473111)
            ·
              refine ⟨15714229468306172184709667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10476152978870781456473111 15714229468306172184709667)
              ·
                refine ⟨23571344202459258277064501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15714229468306172184709667 23571344202459258277064501)
                ·
                  refine ⟨2209813518980555463474797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23571344202459258277064501 2209813518980555463474797)
                  ·
                    refine ⟨828680069617708298803049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2209813518980555463474797 828680069617708298803049)
                    ·
                      rfl

theorem cell22_2420773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 5, 3].length) (baseStart_2420773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2420773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2420773 prefixEnd_2420773 := by exact prefixLift 2420773
  have htrace : WordTrace (prefixWord ++ tailWord_2420773) baseStart_2420773 baseEnd_2420773 := by
    simpa [prefixWord, tailWord_2420773, baseEnd_2420773] using wordTrace_append hprefix tailTrace_2420773
  have hstable : (prefixWord ++ tailWord_2420773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420773).length < 2 ^ (prefixWord ++ tailWord_2420773).sum := by decide
  have hdescent : baseEnd_2420773 < baseStart_2420773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420790 : List Nat := [5, 1, 2, 1, 1, 1, 1, 2, 5, 3]
def baseStart_2420790 : Nat := 118140960795 + 2420790 * 2 ^ 59
def prefixEnd_2420790 : Nat := 4983230072969 + 3 ^ 40 * 2420790 * 2
def baseEnd_2420790 : Nat := 828685889065125921127997

theorem tailTrace_2420790 : CollatzResearch.WordTrace tailWord_2420790 prefixEnd_2420790 828685889065125921127997 := by
  unfold tailWord_2420790
  simp only [CollatzResearch.WordTrace]
  refine ⟨5518341556243671428851739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58862309933265828574418549 5518341556243671428851739)
  ·
    refine ⟨8277512334365507143277609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5518341556243671428851739 8277512334365507143277609)
    ·
      refine ⟨6208134250774130357458207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8277512334365507143277609 6208134250774130357458207)
      ·
        refine ⟨9312201376161195536187311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6208134250774130357458207 9312201376161195536187311)
        ·
          refine ⟨13968302064241793304280967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9312201376161195536187311 13968302064241793304280967)
          ·
            refine ⟨20952453096362689956421451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13968302064241793304280967 20952453096362689956421451)
            ·
              refine ⟨31428679644544034934632177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20952453096362689956421451 31428679644544034934632177)
              ·
                refine ⟨23571509733408026200974133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31428679644544034934632177 23571509733408026200974133)
                ·
                  refine ⟨2209829037507002456341325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23571509733408026200974133 2209829037507002456341325)
                  ·
                    refine ⟨828685889065125921127997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2209829037507002456341325 828685889065125921127997)
                    ·
                      rfl

theorem cell22_2420790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_2420790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2420790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2420790 prefixEnd_2420790 := by exact prefixLift 2420790
  have htrace : WordTrace (prefixWord ++ tailWord_2420790) baseStart_2420790 baseEnd_2420790 := by
    simpa [prefixWord, tailWord_2420790, baseEnd_2420790] using wordTrace_append hprefix tailTrace_2420790
  have hstable : (prefixWord ++ tailWord_2420790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420790).length < 2 ^ (prefixWord ++ tailWord_2420790).sum := by decide
  have hdescent : baseEnd_2420790 < baseStart_2420790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420831 : List Nat := [1, 1, 2, 3, 1, 1, 2, 3, 8]
def baseStart_2420831 : Nat := 118140960795 + 2420831 * 2 ^ 59
def prefixEnd_2420831 : Nat := 4983230072969 + 3 ^ 40 * 2420831 * 2
def baseEnd_2420831 : Nat := 276233308067671826950957

theorem tailTrace_2420831 : CollatzResearch.WordTrace tailWord_2420831 prefixEnd_2420831 276233308067671826950957 := by
  unfold tailWord_2420831
  simp only [CollatzResearch.WordTrace]
  refine ⟨88294960292750206863870347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58863306861833471242580231 88294960292750206863870347)
  ·
    refine ⟨132442440439125310295805521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88294960292750206863870347 132442440439125310295805521)
    ·
      refine ⟨99331830329343982721854141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132442440439125310295805521 99331830329343982721854141)
      ·
        refine ⟨37249436373503993520695303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99331830329343982721854141 37249436373503993520695303)
        ·
          refine ⟨55874154560255990281042955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37249436373503993520695303 55874154560255990281042955)
          ·
            refine ⟨83811231840383985421564433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55874154560255990281042955 83811231840383985421564433)
            ·
              refine ⟨62858423880287989066173325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83811231840383985421564433 62858423880287989066173325)
              ·
                refine ⟨23571908955107995899814997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62858423880287989066173325 23571908955107995899814997)
                ·
                  refine ⟨276233308067671826950957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23571908955107995899814997 276233308067671826950957)
                  ·
                    rfl

theorem cell22_2420831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 8].length) (baseStart_2420831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2420831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2420831 prefixEnd_2420831 := by exact prefixLift 2420831
  have htrace : WordTrace (prefixWord ++ tailWord_2420831) baseStart_2420831 baseEnd_2420831 := by
    simpa [prefixWord, tailWord_2420831, baseEnd_2420831] using wordTrace_append hprefix tailTrace_2420831
  have hstable : (prefixWord ++ tailWord_2420831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420831).length < 2 ^ (prefixWord ++ tailWord_2420831).sum := by decide
  have hdescent : baseEnd_2420831 < baseStart_2420831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420850 : List Nat := [3, 2, 1, 2, 2, 2, 2, 3, 1, 4]
def baseStart_2420850 : Nat := 118140960795 + 2420850 * 2 ^ 59
def prefixEnd_2420850 : Nat := 4983230072969 + 3 ^ 40 * 2420850 * 2
def baseEnd_2420850 : Nat := 828706428291305764627813

theorem tailTrace_2420850 : CollatzResearch.WordTrace tailWord_2420850 prefixEnd_2420850 828706428291305764627813 := by
  unfold tailWord_2420850
  simp only [CollatzResearch.WordTrace]
  refine ⟨22073913319920343277203001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58863768853120915405874669 22073913319920343277203001)
  ·
    refine ⟨16555434989940257457902251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22073913319920343277203001 16555434989940257457902251)
    ·
      refine ⟨24833152484910386186853377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16555434989940257457902251 24833152484910386186853377)
      ·
        refine ⟨18624864363682789640140033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24833152484910386186853377 18624864363682789640140033)
        ·
          refine ⟨13968648272762092230105025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18624864363682789640140033 13968648272762092230105025)
          ·
            refine ⟨10476486204571569172578769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13968648272762092230105025 10476486204571569172578769)
            ·
              refine ⟨7857364653428676879434077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10476486204571569172578769 7857364653428676879434077)
              ·
                refine ⟨2946511745035753829787779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7857364653428676879434077 2946511745035753829787779)
                ·
                  refine ⟨4419767617553630744681669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2946511745035753829787779 4419767617553630744681669)
                  ·
                    refine ⟨828706428291305764627813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4419767617553630744681669 828706428291305764627813)
                    ·
                      rfl

theorem cell22_2420850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_2420850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2420850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2420850 prefixEnd_2420850 := by exact prefixLift 2420850
  have htrace : WordTrace (prefixWord ++ tailWord_2420850) baseStart_2420850 baseEnd_2420850 := by
    simpa [prefixWord, tailWord_2420850, baseEnd_2420850] using wordTrace_append hprefix tailTrace_2420850
  have hstable : (prefixWord ++ tailWord_2420850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420850).length < 2 ^ (prefixWord ++ tailWord_2420850).sum := by decide
  have hdescent : baseEnd_2420850 < baseStart_2420850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420880 : List Nat := [2, 1, 1, 1, 1, 1, 7, 3, 2, 3]
def baseStart_2420880 : Nat := 118140960795 + 2420880 * 2 ^ 59
def prefixEnd_2420880 : Nat := 4983230072969 + 3 ^ 40 * 2420880 * 2
def baseEnd_2420880 : Nat := 828716697904395686377721

theorem tailTrace_2420880 : CollatzResearch.WordTrace tailWord_2420880 prefixEnd_2420880 828716697904395686377721 := by
  unfold tailWord_2420880
  simp only [CollatzResearch.WordTrace]
  refine ⟨44148373734786344116202047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58864498313048458821602729 44148373734786344116202047)
  ·
    refine ⟨66222560602179516174303071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44148373734786344116202047 66222560602179516174303071)
    ·
      refine ⟨99333840903269274261454607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66222560602179516174303071 99333840903269274261454607)
      ·
        refine ⟨149000761354903911392181911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99333840903269274261454607 149000761354903911392181911)
        ·
          refine ⟨223501142032355867088272867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149000761354903911392181911 223501142032355867088272867)
          ·
            refine ⟨335251713048533800632409301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223501142032355867088272867 335251713048533800632409301)
            ·
              refine ⟨7857462024575010952322093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 335251713048533800632409301 7857462024575010952322093)
              ·
                refine ⟨2946548259215629107120785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7857462024575010952322093 2946548259215629107120785)
                ·
                  refine ⟨2209911194411721830340589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2946548259215629107120785 2209911194411721830340589)
                  ·
                    refine ⟨828716697904395686377721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2209911194411721830340589 828716697904395686377721)
                    ·
                      rfl

theorem cell22_2420880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3, 2, 3].length) (baseStart_2420880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2420880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2420880 prefixEnd_2420880 := by exact prefixLift 2420880
  have htrace : WordTrace (prefixWord ++ tailWord_2420880) baseStart_2420880 baseEnd_2420880 := by
    simpa [prefixWord, tailWord_2420880, baseEnd_2420880] using wordTrace_append hprefix tailTrace_2420880
  have hstable : (prefixWord ++ tailWord_2420880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420880).length < 2 ^ (prefixWord ++ tailWord_2420880).sum := by decide
  have hdescent : baseEnd_2420880 < baseStart_2420880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420893 : List Nat := [1, 4, 2, 1, 1, 3, 2, 8]
def baseStart_2420893 : Nat := 118140960795 + 2420893 * 2 ^ 59
def prefixEnd_2420893 : Nat := 4983230072969 + 3 ^ 40 * 2420893 * 2
def baseEnd_2420893 : Nat := 92080127563340887311409

theorem tailTrace_2420893 : CollatzResearch.WordTrace tailWord_2420893 prefixEnd_2420893 92080127563340887311409 := by
  unfold tailWord_2420893
  simp only [CollatzResearch.WordTrace]
  refine ⟨88297221618525591452627333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58864814412350394301751555 88297221618525591452627333)
  ·
    refine ⟨16555729053473548397367625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88297221618525591452627333 16555729053473548397367625)
    ·
      refine ⟨12416796790105161298025719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16555729053473548397367625 12416796790105161298025719)
      ·
        refine ⟨18625195185157741947038579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12416796790105161298025719 18625195185157741947038579)
        ·
          refine ⟨27937792777736612920557869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18625195185157741947038579 27937792777736612920557869)
          ·
            refine ⟨10476672291651229845209201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27937792777736612920557869 10476672291651229845209201)
            ·
              refine ⟨7857504218738422383906901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10476672291651229845209201 7857504218738422383906901)
              ·
                refine ⟨92080127563340887311409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7857504218738422383906901 92080127563340887311409)
                ·
                  rfl

theorem cell22_2420893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 8].length) (baseStart_2420893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2420893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2420893 prefixEnd_2420893 := by exact prefixLift 2420893
  have htrace : WordTrace (prefixWord ++ tailWord_2420893) baseStart_2420893 baseEnd_2420893 := by
    simpa [prefixWord, tailWord_2420893, baseEnd_2420893] using wordTrace_append hprefix tailTrace_2420893
  have hstable : (prefixWord ++ tailWord_2420893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420893).length < 2 ^ (prefixWord ++ tailWord_2420893).sum := by decide
  have hdescent : baseEnd_2420893 < baseStart_2420893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420895 : List Nat := [1, 1, 2, 6, 1, 1, 1, 3, 2, 4]
def baseStart_2420895 : Nat := 118140960795 + 2420895 * 2 ^ 59
def prefixEnd_2420895 : Nat := 4983230072969 + 3 ^ 40 * 2420895 * 2
def baseEnd_2420895 : Nat := 828721832710940647252675

theorem tailTrace_2420895 : CollatzResearch.WordTrace tailWord_2420895 prefixEnd_2420895 828721832710940647252675 := by
  unfold tailWord_2420895
  simp only [CollatzResearch.WordTrace]
  refine ⟨88297294564518345794200139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58864863043012230529466759 88297294564518345794200139)
  ·
    refine ⟨132445941846777518691300209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88297294564518345794200139 132445941846777518691300209)
    ·
      refine ⟨99334456385083139018475157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132445941846777518691300209 99334456385083139018475157)
      ·
        refine ⟨4656302643050772141491023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 99334456385083139018475157 4656302643050772141491023)
        ·
          refine ⟨6984453964576158212236535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4656302643050772141491023 6984453964576158212236535)
          ·
            refine ⟨10476680946864237318354803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6984453964576158212236535 10476680946864237318354803)
            ·
              refine ⟨15715021420296355977532205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10476680946864237318354803 15715021420296355977532205)
              ·
                refine ⟨5893133032611133491574577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15715021420296355977532205 5893133032611133491574577)
                ·
                  refine ⟨4419849774458350118680933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5893133032611133491574577 4419849774458350118680933)
                  ·
                    refine ⟨828721832710940647252675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4419849774458350118680933 828721832710940647252675)
                    ·
                      rfl

theorem cell22_2420895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 2, 4].length) (baseStart_2420895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2420895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2420895 prefixEnd_2420895 := by exact prefixLift 2420895
  have htrace : WordTrace (prefixWord ++ tailWord_2420895) baseStart_2420895 baseEnd_2420895 := by
    simpa [prefixWord, tailWord_2420895, baseEnd_2420895] using wordTrace_append hprefix tailTrace_2420895
  have hstable : (prefixWord ++ tailWord_2420895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420895).length < 2 ^ (prefixWord ++ tailWord_2420895).sum := by decide
  have hdescent : baseEnd_2420895 < baseStart_2420895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420910 : List Nat := [4, 1, 4, 2, 11]
def baseStart_2420910 : Nat := 118140960795 + 2420910 * 2 ^ 59
def prefixEnd_2420910 : Nat := 4983230072969 + 3 ^ 40 * 2420910 * 2
def baseEnd_2420910 : Nat := 3410399043281833778303

theorem tailTrace_2420910 : CollatzResearch.WordTrace tailWord_2420910 prefixEnd_2420910 3410399043281833778303 := by
  unfold tailWord_2420910
  simp only [CollatzResearch.WordTrace]
  refine ⟨11037230207433000419499523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58865227772976002237330789 11037230207433000419499523)
  ·
    refine ⟨16555845311149500629249285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11037230207433000419499523 16555845311149500629249285)
    ·
      refine ⟨3104220995840531367984241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16555845311149500629249285 3104220995840531367984241)
      ·
        refine ⟨2328165746880398525988181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3104220995840531367984241 2328165746880398525988181)
        ·
          refine ⟨3410399043281833778303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2328165746880398525988181 3410399043281833778303)
          ·
            rfl

theorem cell22_2420910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 11].length) (baseStart_2420910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2420910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2420910 prefixEnd_2420910 := by exact prefixLift 2420910
  have htrace : WordTrace (prefixWord ++ tailWord_2420910) baseStart_2420910 baseEnd_2420910 := by
    simpa [prefixWord, tailWord_2420910, baseEnd_2420910] using wordTrace_append hprefix tailTrace_2420910
  have hstable : (prefixWord ++ tailWord_2420910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420910).length < 2 ^ (prefixWord ++ tailWord_2420910).sum := by decide
  have hdescent : baseEnd_2420910 < baseStart_2420910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420925 : List Nat := [1, 4, 1, 2, 1, 1, 1, 5, 3, 3]
def baseStart_2420925 : Nat := 118140960795 + 2420925 * 2 ^ 59
def prefixEnd_2420925 : Nat := 4983230072969 + 3 ^ 40 * 2420925 * 2
def baseEnd_2420925 : Nat := 828732102324030569002583

theorem tailTrace_2420925 : CollatzResearch.WordTrace tailWord_2420925 prefixEnd_2420925 828732102324030569002583 := by
  unfold tailWord_2420925
  simp only [CollatzResearch.WordTrace]
  refine ⟨88298388754409660917792229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58865592502939773945194819 88298388754409660917792229)
  ·
    refine ⟨16555947891451811422086043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88298388754409660917792229 16555947891451811422086043)
    ·
      refine ⟨24833921837177717133129065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16555947891451811422086043 24833921837177717133129065)
      ·
        refine ⟨18625441377883287849846799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24833921837177717133129065 18625441377883287849846799)
        ·
          refine ⟨27938162066824931774770199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18625441377883287849846799 27938162066824931774770199)
          ·
            refine ⟨41907243100237397662155299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27938162066824931774770199 41907243100237397662155299)
            ·
              refine ⟨62860864650356096493232949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41907243100237397662155299 62860864650356096493232949)
              ·
                refine ⟨5893206060970884046240589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62860864650356096493232949 5893206060970884046240589)
                ·
                  refine ⟨2209952272864081517340221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5893206060970884046240589 2209952272864081517340221)
                  ·
                    refine ⟨828732102324030569002583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2209952272864081517340221 828732102324030569002583)
                    ·
                      rfl

theorem cell22_2420925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 3, 3].length) (baseStart_2420925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2420925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2420925 prefixEnd_2420925 := by exact prefixLift 2420925
  have htrace : WordTrace (prefixWord ++ tailWord_2420925) baseStart_2420925 baseEnd_2420925 := by
    simpa [prefixWord, tailWord_2420925, baseEnd_2420925] using wordTrace_append hprefix tailTrace_2420925
  have hstable : (prefixWord ++ tailWord_2420925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420925).length < 2 ^ (prefixWord ++ tailWord_2420925).sum := by decide
  have hdescent : baseEnd_2420925 < baseStart_2420925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420942 : List Nat := [4, 1, 1, 1, 4, 2, 1, 2, 3, 3]
def baseStart_2420942 : Nat := 118140960795 + 2420942 * 2 ^ 59
def prefixEnd_2420942 : Nat := 4983230072969 + 3 ^ 40 * 2420942 * 2
def baseEnd_2420942 : Nat := 828737921771448191327531

theorem tailTrace_2420942 : CollatzResearch.WordTrace tailWord_2420942 prefixEnd_2420942 828737921771448191327531 := by
  unfold tailWord_2420942
  simp only [CollatzResearch.WordTrace]
  refine ⟨11037376099418509102645135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58866005863565381880774053 11037376099418509102645135)
  ·
    refine ⟨16556064149127763653967703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11037376099418509102645135 16556064149127763653967703)
    ·
      refine ⟨24834096223691645480951555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16556064149127763653967703 24834096223691645480951555)
      ·
        refine ⟨37251144335537468221427333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24834096223691645480951555 37251144335537468221427333)
        ·
          refine ⟨6984589562913275291517625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37251144335537468221427333 6984589562913275291517625)
          ·
            refine ⟨5238442172184956468638219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6984589562913275291517625 5238442172184956468638219)
            ·
              refine ⟨7857663258277434702957329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5238442172184956468638219 7857663258277434702957329)
              ·
                refine ⟨5893247443708076027217997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7857663258277434702957329 5893247443708076027217997)
                ·
                  refine ⟨2209967791390528510206749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5893247443708076027217997 2209967791390528510206749)
                  ·
                    refine ⟨828737921771448191327531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2209967791390528510206749 828737921771448191327531)
                    ·
                      rfl

theorem cell22_2420942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 3, 3].length) (baseStart_2420942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2420942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2420942 prefixEnd_2420942 := by exact prefixLift 2420942
  have htrace : WordTrace (prefixWord ++ tailWord_2420942) baseStart_2420942 baseEnd_2420942 := by
    simpa [prefixWord, tailWord_2420942, baseEnd_2420942] using wordTrace_append hprefix tailTrace_2420942
  have hstable : (prefixWord ++ tailWord_2420942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420942).length < 2 ^ (prefixWord ++ tailWord_2420942).sum := by decide
  have hdescent : baseEnd_2420942 < baseStart_2420942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421000 : List Nat := [2, 1, 3, 2, 3, 1, 2, 2, 6]
def baseStart_2421000 : Nat := 118140960795 + 2421000 * 2 ^ 59
def prefixEnd_2421000 : Nat := 4983230072969 + 3 ^ 40 * 2421000 * 2
def baseEnd_2421000 : Nat := 276252592118918457792451

theorem tailTrace_2421000 : CollatzResearch.WordTrace tailWord_2421000 prefixEnd_2421000 276252592118918457792451 := by
  unfold tailWord_2421000
  simp only [CollatzResearch.WordTrace]
  refine ⟨44150562114568974363386227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58867416152758632484514969 44150562114568974363386227)
  ·
    refine ⟨66225843171853461545079341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44150562114568974363386227 66225843171853461545079341)
    ·
      refine ⟨24834691189445048079404753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66225843171853461545079341 24834691189445048079404753)
      ·
        refine ⟨18626018392083786059553565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24834691189445048079404753 18626018392083786059553565)
        ·
          refine ⟨6984756897031419772332587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18626018392083786059553565 6984756897031419772332587)
          ·
            refine ⟨10477135345547129658498881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6984756897031419772332587 10477135345547129658498881)
            ·
              refine ⟨7857851509160347243874161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10477135345547129658498881 7857851509160347243874161)
              ·
                refine ⟨5893388631870260432905621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7857851509160347243874161 5893388631870260432905621)
                ·
                  refine ⟨276252592118918457792451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5893388631870260432905621 276252592118918457792451)
                  ·
                    rfl

theorem cell22_2421000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 6].length) (baseStart_2421000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2421000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2421000 prefixEnd_2421000 := by exact prefixLift 2421000
  have htrace : WordTrace (prefixWord ++ tailWord_2421000) baseStart_2421000 baseEnd_2421000 := by
    simpa [prefixWord, tailWord_2421000, baseEnd_2421000] using wordTrace_append hprefix tailTrace_2421000
  have hstable : (prefixWord ++ tailWord_2421000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421000).length < 2 ^ (prefixWord ++ tailWord_2421000).sum := by decide
  have hdescent : baseEnd_2421000 < baseStart_2421000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421034 : List Nat := [3, 1, 4, 2, 2, 2, 1, 1, 6]
def baseStart_2421034 : Nat := 118140960795 + 2421034 * 2 ^ 59
def prefixEnd_2421034 : Nat := 4983230072969 + 3 ^ 40 * 2421034 * 2
def baseEnd_2421034 : Nat := 276256471750530206009083

theorem tailTrace_2421034 : CollatzResearch.WordTrace tailWord_2421034 prefixEnd_2421034 276256471750530206009083 := by
  unfold tailWord_2421034
  simp only [CollatzResearch.WordTrace]
  refine ⟨22075591077753693133377539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58868242874009848355673437 22075591077753693133377539)
  ·
    refine ⟨33113386616630539700066309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22075591077753693133377539 33113386616630539700066309)
    ·
      refine ⟨6208759990618226193762433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33113386616630539700066309 6208759990618226193762433)
      ·
        refine ⟨4656569992963669645321825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6208759990618226193762433 4656569992963669645321825)
        ·
          refine ⟨3492427494722752233991369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4656569992963669645321825 3492427494722752233991369)
          ·
            refine ⟨2619320621042064175493527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3492427494722752233991369 2619320621042064175493527)
            ·
              refine ⟨3928980931563096263240291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2619320621042064175493527 3928980931563096263240291)
              ·
                refine ⟨5893471397344644394860437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3928980931563096263240291 5893471397344644394860437)
                ·
                  refine ⟨276256471750530206009083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5893471397344644394860437 276256471750530206009083)
                  ·
                    rfl

theorem cell22_2421034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 6].length) (baseStart_2421034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2421034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2421034 prefixEnd_2421034 := by exact prefixLift 2421034
  have htrace : WordTrace (prefixWord ++ tailWord_2421034) baseStart_2421034 baseEnd_2421034 := by
    simpa [prefixWord, tailWord_2421034, baseEnd_2421034] using wordTrace_append hprefix tailTrace_2421034
  have hstable : (prefixWord ++ tailWord_2421034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421034).length < 2 ^ (prefixWord ++ tailWord_2421034).sum := by decide
  have hdescent : baseEnd_2421034 < baseStart_2421034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421045 : List Nat := [1, 3, 3, 1, 2, 1, 4, 7]
def baseStart_2421045 : Nat := 118140960795 + 2421045 * 2 ^ 59
def prefixEnd_2421045 : Nat := 4983230072969 + 3 ^ 40 * 2421045 * 2
def baseEnd_2421045 : Nat := 92085908975154472889135

theorem tailTrace_2421045 : CollatzResearch.WordTrace tailWord_2421045 prefixEnd_2421045 92085908975154472889135 := by
  unfold tailWord_2421045
  simp only [CollatzResearch.WordTrace]
  refine ⟨88302765513974921412160589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58868510342649947608107059 88302765513974921412160589)
  ·
    refine ⟨33113537067740595529560221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88302765513974921412160589 33113537067740595529560221)
    ·
      refine ⟨12417576400402723323585083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33113537067740595529560221 12417576400402723323585083)
      ·
        refine ⟨18626364600604084985377625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12417576400402723323585083 18626364600604084985377625)
        ·
          refine ⟨13969773450453063739033219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18626364600604084985377625 13969773450453063739033219)
          ·
            refine ⟨20954660175679595608549829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13969773450453063739033219 20954660175679595608549829)
            ·
              refine ⟨3928998782939924176603093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20954660175679595608549829 3928998782939924176603093)
              ·
                refine ⟨92085908975154472889135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3928998782939924176603093 92085908975154472889135)
                ·
                  rfl

theorem cell22_2421045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 7].length) (baseStart_2421045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2421045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2421045 prefixEnd_2421045 := by exact prefixLift 2421045
  have htrace : WordTrace (prefixWord ++ tailWord_2421045) baseStart_2421045 baseEnd_2421045 := by
    simpa [prefixWord, tailWord_2421045, baseEnd_2421045] using wordTrace_append hprefix tailTrace_2421045
  have hstable : (prefixWord ++ tailWord_2421045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421045).length < 2 ^ (prefixWord ++ tailWord_2421045).sum := by decide
  have hdescent : baseEnd_2421045 < baseStart_2421045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421049 : List Nat := [1, 2, 1, 6, 1, 2, 1, 3, 2, 3]
def baseStart_2421049 : Nat := 118140960795 + 2421049 * 2 ^ 59
def prefixEnd_2421049 : Nat := 4983230072969 + 3 ^ 40 * 2421049 * 2
def baseEnd_2421049 : Nat := 828774550058135578902203

theorem tailTrace_2421049 : CollatzResearch.WordTrace tailWord_2421049 prefixEnd_2421049 828774550058135578902203 := by
  unfold tailWord_2421049
  simp only [CollatzResearch.WordTrace]
  refine ⟨88302911405960430095306201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58868607603973620063537467 88302911405960430095306201)
  ·
    refine ⟨66227183554470322571479651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88302911405960430095306201 66227183554470322571479651)
    ·
      refine ⟨99340775331705483857219477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66227183554470322571479651 99340775331705483857219477)
      ·
        refine ⟨4656598843673694555807163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 99340775331705483857219477 4656598843673694555807163)
        ·
          refine ⟨6984898265510541833710745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4656598843673694555807163 6984898265510541833710745)
          ·
            refine ⟨5238673699132906375283059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6984898265510541833710745 5238673699132906375283059)
            ·
              refine ⟨7858010548699359562924589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5238673699132906375283059 7858010548699359562924589)
              ·
                refine ⟨2946753955762259836096721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7858010548699359562924589 2946753955762259836096721)
                ·
                  refine ⟨2210065466821694877072541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2946753955762259836096721 2210065466821694877072541)
                  ·
                    refine ⟨828774550058135578902203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2210065466821694877072541 828774550058135578902203)
                    ·
                      rfl

theorem cell22_2421049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3, 2, 3].length) (baseStart_2421049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2421049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2421049 prefixEnd_2421049 := by exact prefixLift 2421049
  have htrace : WordTrace (prefixWord ++ tailWord_2421049) baseStart_2421049 baseEnd_2421049 := by
    simpa [prefixWord, tailWord_2421049, baseEnd_2421049] using wordTrace_append hprefix tailTrace_2421049
  have hstable : (prefixWord ++ tailWord_2421049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421049).length < 2 ^ (prefixWord ++ tailWord_2421049).sum := by decide
  have hdescent : baseEnd_2421049 < baseStart_2421049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421152 : List Nat := [2, 1, 1, 4, 1, 4, 2, 1, 6]
def baseStart_2421152 : Nat := 118140960795 + 2421152 * 2 ^ 59
def prefixEnd_2421152 : Nat := 4983230072969 + 3 ^ 40 * 2421152 * 2
def baseEnd_2421152 : Nat := 276269936354359214525629

theorem tailTrace_2421152 : CollatzResearch.WordTrace tailWord_2421152 prefixEnd_2421152 276269936354359214525629 := by
  unfold tailWord_2421152
  simp only [CollatzResearch.WordTrace]
  refine ⟨44153334062293639343152855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58871112083058185790870473 44153334062293639343152855)
  ·
    refine ⟨66230001093440459014729283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44153334062293639343152855 66230001093440459014729283)
    ·
      refine ⟨99345001640160688522093925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66230001093440459014729283 99345001640160688522093925)
      ·
        refine ⟨18627187807530129097892611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99345001640160688522093925 18627187807530129097892611)
        ·
          refine ⟨27940781711295193646838917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18627187807530129097892611 27940781711295193646838917)
          ·
            refine ⟨5238896570867848808782297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27940781711295193646838917 5238896570867848808782297)
            ·
              refine ⟨3929172428150886606586723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5238896570867848808782297 3929172428150886606586723)
              ·
                refine ⟨5893758642226329909880085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3929172428150886606586723 5893758642226329909880085)
                ·
                  refine ⟨276269936354359214525629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5893758642226329909880085 276269936354359214525629)
                  ·
                    rfl

theorem cell22_2421152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 6].length) (baseStart_2421152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2421152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2421152 prefixEnd_2421152 := by exact prefixLift 2421152
  have htrace : WordTrace (prefixWord ++ tailWord_2421152) baseStart_2421152 baseEnd_2421152 := by
    simpa [prefixWord, tailWord_2421152, baseEnd_2421152] using wordTrace_append hprefix tailTrace_2421152
  have hstable : (prefixWord ++ tailWord_2421152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421152).length < 2 ^ (prefixWord ++ tailWord_2421152).sum := by decide
  have hdescent : baseEnd_2421152 < baseStart_2421152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421182 : List Nat := [4, 2, 1, 1, 1, 1, 4, 1, 1, 6]
def baseStart_2421182 : Nat := 118140960795 + 2421182 * 2 ^ 59
def prefixEnd_2421182 : Nat := 4983230072969 + 3 ^ 40 * 2421182 * 2
def baseEnd_2421182 : Nat := 828820078676167565326795

theorem tailTrace_2421182 : CollatzResearch.WordTrace tailWord_2421182 prefixEnd_2421182 828820078676167565326795 := by
  unfold tailWord_2421182
  simp only [CollatzResearch.WordTrace]
  refine ⟨11038470289309824226237225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58871841542985729206598533 11038470289309824226237225)
  ·
    refine ⟨8278852716982368169677919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11038470289309824226237225 8278852716982368169677919)
    ·
      refine ⟨12418279075473552254516879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8278852716982368169677919 12418279075473552254516879)
      ·
        refine ⟨18627418613210328381775319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12418279075473552254516879 18627418613210328381775319)
        ·
          refine ⟨27941127919815492572662979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18627418613210328381775319 27941127919815492572662979)
          ·
            refine ⟨41911691879723238858994469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27941127919815492572662979 41911691879723238858994469)
            ·
              refine ⟨7858442227448107286061463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41911691879723238858994469 7858442227448107286061463)
              ·
                refine ⟨11787663341172160929092195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7858442227448107286061463 11787663341172160929092195)
                ·
                  refine ⟨17681495011758241393638293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11787663341172160929092195 17681495011758241393638293)
                  ·
                    refine ⟨828820078676167565326795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17681495011758241393638293 828820078676167565326795)
                    ·
                      rfl

theorem cell22_2421182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_2421182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2421182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2421182 prefixEnd_2421182 := by exact prefixLift 2421182
  have htrace : WordTrace (prefixWord ++ tailWord_2421182) baseStart_2421182 baseEnd_2421182 := by
    simpa [prefixWord, tailWord_2421182, baseEnd_2421182] using wordTrace_append hprefix tailTrace_2421182
  have hstable : (prefixWord ++ tailWord_2421182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421182).length < 2 ^ (prefixWord ++ tailWord_2421182).sum := by decide
  have hdescent : baseEnd_2421182 < baseStart_2421182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421225 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 9]
def baseStart_2421225 : Nat := 118140960795 + 2421225 * 2 ^ 59
def prefixEnd_2421225 : Nat := 4983230072969 + 3 ^ 40 * 2421225 * 2
def baseEnd_2421225 : Nat := 276278266151643262167221

theorem tailTrace_2421225 : CollatzResearch.WordTrace tailWord_2421225 prefixEnd_2421225 276278266151643262167221 := by
  unfold tailWord_2421225
  simp only [CollatzResearch.WordTrace]
  refine ⟨88309330653322812153713129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58872887102215208102475419 88309330653322812153713129)
  ·
    refine ⟨66231997989992109115284847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88309330653322812153713129 66231997989992109115284847)
    ·
      refine ⟨99347996984988163672927271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66231997989992109115284847 99347996984988163672927271)
      ·
        refine ⟨149021995477482245509390907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99347996984988163672927271 149021995477482245509390907)
        ·
          refine ⟨223532993216223368264086361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149021995477482245509390907 223532993216223368264086361)
          ·
            refine ⟨167649744912167526198064771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 223532993216223368264086361 167649744912167526198064771)
            ·
              refine ⟨251474617368251289297097157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167649744912167526198064771 251474617368251289297097157)
              ·
                refine ⟨47151490756547116743205717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 251474617368251289297097157 47151490756547116743205717)
                ·
                  refine ⟨276278266151643262167221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 47151490756547116743205717 276278266151643262167221)
                  ·
                    rfl

theorem cell22_2421225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 9].length) (baseStart_2421225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2421225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2421225 prefixEnd_2421225 := by exact prefixLift 2421225
  have htrace : WordTrace (prefixWord ++ tailWord_2421225) baseStart_2421225 baseEnd_2421225 := by
    simpa [prefixWord, tailWord_2421225, baseEnd_2421225] using wordTrace_append hprefix tailTrace_2421225
  have hstable : (prefixWord ++ tailWord_2421225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421225).length < 2 ^ (prefixWord ++ tailWord_2421225).sum := by decide
  have hdescent : baseEnd_2421225 < baseStart_2421225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421259 : List Nat := [1, 1, 1, 1, 7, 2, 2, 2, 5]
def baseStart_2421259 : Nat := 118140960795 + 2421259 * 2 ^ 59
def prefixEnd_2421259 : Nat := 4983230072969 + 3 ^ 40 * 2421259 * 2
def baseEnd_2421259 : Nat := 276282145783255010383853

theorem tailTrace_2421259 : CollatzResearch.WordTrace tailWord_2421259 prefixEnd_2421259 276282145783255010383853 := by
  unfold tailWord_2421259
  simp only [CollatzResearch.WordTrace]
  refine ⟨88310570735199635960450831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58873713823466423973633887 88310570735199635960450831)
  ·
    refine ⟨132465856102799453940676247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88310570735199635960450831 132465856102799453940676247)
    ·
      refine ⟨198698784154199180911014371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132465856102799453940676247 198698784154199180911014371)
      ·
        refine ⟨298048176231298771366521557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198698784154199180911014371 298048176231298771366521557)
        ·
          refine ⟨6985504130421064953902849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 298048176231298771366521557 6985504130421064953902849)
          ·
            refine ⟨5239128097815798715427137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6985504130421064953902849 5239128097815798715427137)
            ·
              refine ⟨3929346073361849036570353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5239128097815798715427137 3929346073361849036570353)
              ·
                refine ⟨2947009555021386777427765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3929346073361849036570353 2947009555021386777427765)
                ·
                  refine ⟨276282145783255010383853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2947009555021386777427765 276282145783255010383853)
                  ·
                    rfl

theorem cell22_2421259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2, 5].length) (baseStart_2421259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2421259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2421259 prefixEnd_2421259 := by exact prefixLift 2421259
  have htrace : WordTrace (prefixWord ++ tailWord_2421259) baseStart_2421259 baseEnd_2421259 := by
    simpa [prefixWord, tailWord_2421259, baseEnd_2421259] using wordTrace_append hprefix tailTrace_2421259
  have hstable : (prefixWord ++ tailWord_2421259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421259).length < 2 ^ (prefixWord ++ tailWord_2421259).sum := by decide
  have hdescent : baseEnd_2421259 < baseStart_2421259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421261 : List Nat := [1, 7, 1, 1, 1, 1, 1, 1, 2, 6]
def baseStart_2421261 : Nat := 118140960795 + 2421261 * 2 ^ 59
def prefixEnd_2421261 : Nat := 4983230072969 + 3 ^ 40 * 2421261 * 2
def baseEnd_2421261 : Nat := 828847121990637692601553

theorem tailTrace_2421261 : CollatzResearch.WordTrace tailWord_2421261 prefixEnd_2421261 828847121990637692601553 := by
  unfold tailWord_2421261
  simp only [CollatzResearch.WordTrace]
  refine ⟨88310643681192390302023637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58873762454128260201349091 88310643681192390302023637)
  ·
    refine ⟨2069780711277946647703679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 88310643681192390302023637 2069780711277946647703679)
    ·
      refine ⟨3104671066916919971555519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2069780711277946647703679 3104671066916919971555519)
      ·
        refine ⟨4657006600375379957333279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3104671066916919971555519 4657006600375379957333279)
        ·
          refine ⟨6985509900563069935999919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4657006600375379957333279 6985509900563069935999919)
          ·
            refine ⟨10478264850844604903999879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6985509900563069935999919 10478264850844604903999879)
            ·
              refine ⟨15717397276266907355999819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10478264850844604903999879 15717397276266907355999819)
              ·
                refine ⟨23576095914400361033999729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15717397276266907355999819 23576095914400361033999729)
                ·
                  refine ⟨17682071935800270775499797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23576095914400361033999729 17682071935800270775499797)
                  ·
                    refine ⟨828847121990637692601553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17682071935800270775499797 828847121990637692601553)
                    ·
                      rfl

theorem cell22_2421261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_2421261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2421261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2421261 prefixEnd_2421261 := by exact prefixLift 2421261
  have htrace : WordTrace (prefixWord ++ tailWord_2421261) baseStart_2421261 baseEnd_2421261 := by
    simpa [prefixWord, tailWord_2421261, baseEnd_2421261] using wordTrace_append hprefix tailTrace_2421261
  have hstable : (prefixWord ++ tailWord_2421261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421261).length < 2 ^ (prefixWord ++ tailWord_2421261).sum := by decide
  have hdescent : baseEnd_2421261 < baseStart_2421261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421306 : List Nat := [3, 1, 1, 1, 3, 3, 4, 1, 1, 4]
def baseStart_2421306 : Nat := 118140960795 + 2421306 * 2 ^ 59
def prefixEnd_2421306 : Nat := 4983230072969 + 3 ^ 40 * 2421306 * 2
def baseEnd_2421306 : Nat := 828862526410272575226415

theorem tailTrace_2421306 : CollatzResearch.WordTrace tailWord_2421306 prefixEnd_2421306 828862526410272575226415 := by
  unfold tailWord_2421306
  simp only [CollatzResearch.WordTrace]
  refine ⟨22078071241507340746852943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58874856644019575324941181 22078071241507340746852943)
  ·
    refine ⟨33117106862261011120279415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22078071241507340746852943 33117106862261011120279415)
    ·
      refine ⟨49675660293391516680419123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33117106862261011120279415 49675660293391516680419123)
      ·
        refine ⟨74513490440087275020628685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49675660293391516680419123 74513490440087275020628685)
        ·
          refine ⟨27942558915032728132735757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74513490440087275020628685 27942558915032728132735757)
          ·
            refine ⟨10478459593137273049775909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27942558915032728132735757 10478459593137273049775909)
            ·
              refine ⟨1964711173713238696832983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10478459593137273049775909 1964711173713238696832983)
              ·
                refine ⟨2947066760569858045249475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1964711173713238696832983 2947066760569858045249475)
                ·
                  refine ⟨4420600140854787067874213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2947066760569858045249475 4420600140854787067874213)
                  ·
                    refine ⟨828862526410272575226415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4420600140854787067874213 828862526410272575226415)
                    ·
                      rfl

theorem cell22_2421306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 1, 1, 4].length) (baseStart_2421306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2421306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2421306 prefixEnd_2421306 := by exact prefixLift 2421306
  have htrace : WordTrace (prefixWord ++ tailWord_2421306) baseStart_2421306 baseEnd_2421306 := by
    simpa [prefixWord, tailWord_2421306, baseEnd_2421306] using wordTrace_append hprefix tailTrace_2421306
  have hstable : (prefixWord ++ tailWord_2421306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421306).length < 2 ^ (prefixWord ++ tailWord_2421306).sum := by decide
  have hdescent : baseEnd_2421306 < baseStart_2421306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421310 : List Nat := [4, 2, 1, 4, 2, 1, 1, 2, 5]
def baseStart_2421310 : Nat := 118140960795 + 2421310 * 2 ^ 59
def prefixEnd_2421310 : Nat := 4983230072969 + 3 ^ 40 * 2421310 * 2
def baseEnd_2421310 : Nat := 276287965230672632708801

theorem tailTrace_2421310 : CollatzResearch.WordTrace tailWord_2421310 prefixEnd_2421310 276287965230672632708801 := by
  unfold tailWord_2421310
  simp only [CollatzResearch.WordTrace]
  refine ⟨11039053857251858958819673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58874953905343247780371589 11039053857251858958819673)
  ·
    refine ⟨8279290392938894219114755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11039053857251858958819673 8279290392938894219114755)
    ·
      refine ⟨12418935589408341328672133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8279290392938894219114755 12418935589408341328672133)
      ·
        refine ⟨2328550423014063999126025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12418935589408341328672133 2328550423014063999126025)
        ·
          refine ⟨1746412817260547999344519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2328550423014063999126025 1746412817260547999344519)
          ·
            refine ⟨2619619225890821999016779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1746412817260547999344519 2619619225890821999016779)
            ·
              refine ⟨3929428838836232998525169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2619619225890821999016779 3929428838836232998525169)
              ·
                refine ⟨2947071629127174748893877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3929428838836232998525169 2947071629127174748893877)
                ·
                  refine ⟨276287965230672632708801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2947071629127174748893877 276287965230672632708801)
                  ·
                    rfl

theorem cell22_2421310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_2421310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2421310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2421310 prefixEnd_2421310 := by exact prefixLift 2421310
  have htrace : WordTrace (prefixWord ++ tailWord_2421310) baseStart_2421310 baseEnd_2421310 := by
    simpa [prefixWord, tailWord_2421310, baseEnd_2421310] using wordTrace_append hprefix tailTrace_2421310
  have hstable : (prefixWord ++ tailWord_2421310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421310).length < 2 ^ (prefixWord ++ tailWord_2421310).sum := by decide
  have hdescent : baseEnd_2421310 < baseStart_2421310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421347 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 2, 7]
def baseStart_2421347 : Nat := 118140960795 + 2421347 * 2 ^ 59
def prefixEnd_2421347 : Nat := 4983230072969 + 3 ^ 40 * 2421347 * 2
def baseEnd_2421347 : Nat := 828876561548162134951289

theorem tailTrace_2421347 : CollatzResearch.WordTrace tailWord_2421347 prefixEnd_2421347 828876561548162134951289 := by
  unfold tailWord_2421347
  simp only [CollatzResearch.WordTrace]
  refine ⟨88313780358880826989654295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58875853572587217993102863 88313780358880826989654295)
  ·
    refine ⟨132470670538321240484481443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88313780358880826989654295 132470670538321240484481443)
    ·
      refine ⟨198706005807481860726722165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132470670538321240484481443 198706005807481860726722165)
      ·
        refine ⟨18628688044451424443130203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 198706005807481860726722165 18628688044451424443130203)
        ·
          refine ⟨27943032066677136664695305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18628688044451424443130203 27943032066677136664695305)
          ·
            refine ⟨20957274050007852498521479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27943032066677136664695305 20957274050007852498521479)
            ·
              refine ⟨31435911075011778747782219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20957274050007852498521479 31435911075011778747782219)
              ·
                refine ⟨47153866612517668121673329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31435911075011778747782219 47153866612517668121673329)
                ·
                  refine ⟨35365399959388251091254997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47153866612517668121673329 35365399959388251091254997)
                  ·
                    refine ⟨828876561548162134951289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35365399959388251091254997 828876561548162134951289)
                    ·
                      rfl

theorem cell22_2421347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 7].length) (baseStart_2421347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2421347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2421347 prefixEnd_2421347 := by exact prefixLift 2421347
  have htrace : WordTrace (prefixWord ++ tailWord_2421347) baseStart_2421347 baseEnd_2421347 := by
    simpa [prefixWord, tailWord_2421347, baseEnd_2421347] using wordTrace_append hprefix tailTrace_2421347
  have hstable : (prefixWord ++ tailWord_2421347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421347).length < 2 ^ (prefixWord ++ tailWord_2421347).sum := by decide
  have hdescent : baseEnd_2421347 < baseStart_2421347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421349 : List Nat := [1, 3, 1, 3, 4, 1, 1, 8]
def baseStart_2421349 : Nat := 118140960795 + 2421349 * 2 ^ 59
def prefixEnd_2421349 : Nat := 4983230072969 + 3 ^ 40 * 2421349 * 2
def baseEnd_2421349 : Nat := 92097471798781644044587

theorem tailTrace_2421349 : CollatzResearch.WordTrace tailWord_2421349 prefixEnd_2421349 92097471798781644044587 := by
  unfold tailWord_2421349
  simp only [CollatzResearch.WordTrace]
  refine ⟨88313853304873581331227101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58875902203249054220818067 88313853304873581331227101)
  ·
    refine ⟨33117694989327592999210163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88313853304873581331227101 33117694989327592999210163)
    ·
      refine ⟨49676542483991389498815245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33117694989327592999210163 49676542483991389498815245)
      ·
        refine ⟨18628703431496771062055717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49676542483991389498815245 18628703431496771062055717)
        ·
          refine ⟨3492881893405644574135447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18628703431496771062055717 3492881893405644574135447)
          ·
            refine ⟨5239322840108466861203171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3492881893405644574135447 5239322840108466861203171)
            ·
              refine ⟨7858984260162700291804757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5239322840108466861203171 7858984260162700291804757)
              ·
                refine ⟨92097471798781644044587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7858984260162700291804757 92097471798781644044587)
                ·
                  rfl

theorem cell22_2421349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 8].length) (baseStart_2421349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2421349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2421349 prefixEnd_2421349 := by exact prefixLift 2421349
  have htrace : WordTrace (prefixWord ++ tailWord_2421349) baseStart_2421349 baseEnd_2421349 := by
    simpa [prefixWord, tailWord_2421349, baseEnd_2421349] using wordTrace_append hprefix tailTrace_2421349
  have hstable : (prefixWord ++ tailWord_2421349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421349).length < 2 ^ (prefixWord ++ tailWord_2421349).sum := by decide
  have hdescent : baseEnd_2421349 < baseStart_2421349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421366 : List Nat := [5, 1, 1, 2, 3, 2, 8]
def baseStart_2421366 : Nat := 118140960795 + 2421366 * 2 ^ 59
def prefixEnd_2421366 : Nat := 4983230072969 + 3 ^ 40 * 2421366 * 2
def baseEnd_2421366 : Nat := 30699372801350089582453

theorem tailTrace_2421366 : CollatzResearch.WordTrace tailWord_2421366 prefixEnd_2421366 30699372801350089582453 := by
  unfold tailWord_2421366
  simp only [CollatzResearch.WordTrace]
  refine ⟨5519654584113249577162247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58876315563874662156397301 5519654584113249577162247)
  ·
    refine ⟨8279481876169874365743371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5519654584113249577162247 8279481876169874365743371)
    ·
      refine ⟨12419222814254811548615057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8279481876169874365743371 12419222814254811548615057)
      ·
        refine ⟨9314417110691108661461293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12419222814254811548615057 9314417110691108661461293)
        ·
          refine ⟨3492906416509165748047985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9314417110691108661461293 3492906416509165748047985)
          ·
            refine ⟨2619679812381874311035989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3492906416509165748047985 2619679812381874311035989)
            ·
              refine ⟨30699372801350089582453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2619679812381874311035989 30699372801350089582453)
              ·
                rfl

theorem cell22_2421366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 8].length) (baseStart_2421366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2421366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2421366 prefixEnd_2421366 := by exact prefixLift 2421366
  have htrace : WordTrace (prefixWord ++ tailWord_2421366) baseStart_2421366 baseEnd_2421366 := by
    simpa [prefixWord, tailWord_2421366, baseEnd_2421366] using wordTrace_append hprefix tailTrace_2421366
  have hstable : (prefixWord ++ tailWord_2421366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421366).length < 2 ^ (prefixWord ++ tailWord_2421366).sum := by decide
  have hdescent : baseEnd_2421366 < baseStart_2421366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421381 : List Nat := [1, 3, 1, 1, 4, 2, 3, 1, 3, 3]
def baseStart_2421381 : Nat := 118140960795 + 2421381 * 2 ^ 59
def prefixEnd_2421381 : Nat := 4983230072969 + 3 ^ 40 * 2421381 * 2
def baseEnd_2421381 : Nat := 828888200442997379601185

theorem tailTrace_2421381 : CollatzResearch.WordTrace tailWord_2421381 prefixEnd_2421381 828888200442997379601185 := by
  unfold tailWord_2421381
  simp only [CollatzResearch.WordTrace]
  refine ⟨88315020440757650796391997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58876680293838433864261331 88315020440757650796391997)
  ·
    refine ⟨33118132665284119048646999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88315020440757650796391997 33118132665284119048646999)
    ·
      refine ⟨49677198997926178572970499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33118132665284119048646999 49677198997926178572970499)
      ·
        refine ⟨74515798496889267859455749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49677198997926178572970499 74515798496889267859455749)
        ·
          refine ⟨13971712218166737723647953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74515798496889267859455749 13971712218166737723647953)
          ·
            refine ⟨10478784163625053292735965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13971712218166737723647953 10478784163625053292735965)
            ·
              refine ⟨3929544061359394984775987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10478784163625053292735965 3929544061359394984775987)
              ·
                refine ⟨5894316092039092477163981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3929544061359394984775987 5894316092039092477163981)
                ·
                  refine ⟨2210368534514659678936493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5894316092039092477163981 2210368534514659678936493)
                  ·
                    refine ⟨828888200442997379601185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2210368534514659678936493 828888200442997379601185)
                    ·
                      rfl

theorem cell22_2421381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 3, 3].length) (baseStart_2421381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2421381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2421381 prefixEnd_2421381 := by exact prefixLift 2421381
  have htrace : WordTrace (prefixWord ++ tailWord_2421381) baseStart_2421381 baseEnd_2421381 := by
    simpa [prefixWord, tailWord_2421381, baseEnd_2421381] using wordTrace_append hprefix tailTrace_2421381
  have hstable : (prefixWord ++ tailWord_2421381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421381).length < 2 ^ (prefixWord ++ tailWord_2421381).sum := by decide
  have hdescent : baseEnd_2421381 < baseStart_2421381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421473 : List Nat := [1, 2, 3, 1, 4, 2, 2, 3, 4]
def baseStart_2421473 : Nat := 118140960795 + 2421473 * 2 ^ 59
def prefixEnd_2421473 : Nat := 4983230072969 + 3 ^ 40 * 2421473 * 2
def baseEnd_2421473 : Nat := 276306564641046602100301

theorem tailTrace_2421473 : CollatzResearch.WordTrace tailWord_2421473 prefixEnd_2421473 276306564641046602100301 := by
  unfold tailWord_2421473
  simp only [CollatzResearch.WordTrace]
  refine ⟨88318375956424350508741073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58878917304282900339160715 88318375956424350508741073)
  ·
    refine ⟨66238781967318262881555805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88318375956424350508741073 66238781967318262881555805)
    ·
      refine ⟨24839543237744348580583427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66238781967318262881555805 24839543237744348580583427)
      ·
        refine ⟨37259314856616522870875141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24839543237744348580583427 37259314856616522870875141)
        ·
          refine ⟨6986121535615598038289089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37259314856616522870875141 6986121535615598038289089)
          ·
            refine ⟨5239591151711698528716817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6986121535615598038289089 5239591151711698528716817)
            ·
              refine ⟨3929693363783773896537613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5239591151711698528716817 3929693363783773896537613)
              ·
                refine ⟨1473635011418915211201605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3929693363783773896537613 1473635011418915211201605)
                ·
                  refine ⟨276306564641046602100301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1473635011418915211201605 276306564641046602100301)
                  ·
                    rfl

theorem cell22_2421473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 3, 4].length) (baseStart_2421473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2421473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2421473 prefixEnd_2421473 := by exact prefixLift 2421473
  have htrace : WordTrace (prefixWord ++ tailWord_2421473) baseStart_2421473 baseEnd_2421473 := by
    simpa [prefixWord, tailWord_2421473, baseEnd_2421473] using wordTrace_append hprefix tailTrace_2421473
  have hstable : (prefixWord ++ tailWord_2421473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421473).length < 2 ^ (prefixWord ++ tailWord_2421473).sum := by decide
  have hdescent : baseEnd_2421473 < baseStart_2421473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421475 : List Nat := [1, 1, 1, 7, 1, 3, 2, 1, 1, 4]
def baseStart_2421475 : Nat := 118140960795 + 2421475 * 2 ^ 59
def prefixEnd_2421475 : Nat := 4983230072969 + 3 ^ 40 * 2421475 * 2
def baseEnd_2421475 : Nat := 828920378564012467750897

theorem tailTrace_2421475 : CollatzResearch.WordTrace tailWord_2421475 prefixEnd_2421475 828920378564012467750897 := by
  unfold tailWord_2421475
  simp only [CollatzResearch.WordTrace]
  refine ⟨88318448902417104850313879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58878965934944736566875919 88318448902417104850313879)
  ·
    refine ⟨132477673353625657275470819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88318448902417104850313879 132477673353625657275470819)
    ·
      refine ⟨198716510030438485913206229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132477673353625657275470819 198716510030438485913206229)
      ·
        refine ⟨4657418203838402013590771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 198716510030438485913206229 4657418203838402013590771)
        ·
          refine ⟨6986127305757603020386157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4657418203838402013590771 6986127305757603020386157)
          ·
            refine ⟨2619797739659101132644809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6986127305757603020386157 2619797739659101132644809)
            ·
              refine ⟨1964848304744325849483607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2619797739659101132644809 1964848304744325849483607)
              ·
                refine ⟨2947272457116488774225411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1964848304744325849483607 2947272457116488774225411)
                ·
                  refine ⟨4420908685674733161338117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2947272457116488774225411 4420908685674733161338117)
                  ·
                    refine ⟨828920378564012467750897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4420908685674733161338117 828920378564012467750897)
                    ·
                      rfl

theorem cell22_2421475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 1, 1, 4].length) (baseStart_2421475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2421475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2421475 prefixEnd_2421475 := by exact prefixLift 2421475
  have htrace : WordTrace (prefixWord ++ tailWord_2421475) baseStart_2421475 baseEnd_2421475 := by
    simpa [prefixWord, tailWord_2421475, baseEnd_2421475] using wordTrace_append hprefix tailTrace_2421475
  have hstable : (prefixWord ++ tailWord_2421475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421475).length < 2 ^ (prefixWord ++ tailWord_2421475).sum := by decide
  have hdescent : baseEnd_2421475 < baseStart_2421475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421550 : List Nat := [4, 1, 3, 2, 1, 1, 3, 1, 3, 3]
def baseStart_2421550 : Nat := 118140960795 + 2421550 * 2 ^ 59
def prefixEnd_2421550 : Nat := 4983230072969 + 3 ^ 40 * 2421550 * 2
def baseEnd_2421550 : Nat := 828946052596737272125667

theorem tailTrace_2421550 : CollatzResearch.WordTrace tailWord_2421550 prefixEnd_2421550 828946052596737272125667 := by
  unfold tailWord_2421550
  simp only [CollatzResearch.WordTrace]
  refine ⟨11040148047143174082411763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58880789584763595106196069 11040148047143174082411763)
  ·
    refine ⟨16560222070714761123617645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11040148047143174082411763 16560222070714761123617645)
    ·
      refine ⟨6210083276518035421356617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16560222070714761123617645 6210083276518035421356617)
      ·
        refine ⟨4657562457388526566017463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6210083276518035421356617 4657562457388526566017463)
        ·
          refine ⟨6986343686082789849026195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4657562457388526566017463 6986343686082789849026195)
          ·
            refine ⟨10479515529124184773539293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6986343686082789849026195 10479515529124184773539293)
            ·
              refine ⟨3929818323421569290077235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10479515529124184773539293 3929818323421569290077235)
              ·
                refine ⟨5894727485132353935115853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3929818323421569290077235 5894727485132353935115853)
                ·
                  refine ⟨2210522806924632725668445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5894727485132353935115853 2210522806924632725668445)
                  ·
                    refine ⟨828946052596737272125667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2210522806924632725668445 828946052596737272125667)
                    ·
                      rfl

theorem cell22_2421550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_2421550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2421550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2421550 prefixEnd_2421550 := by exact prefixLift 2421550
  have htrace : WordTrace (prefixWord ++ tailWord_2421550) baseStart_2421550 baseEnd_2421550 := by
    simpa [prefixWord, tailWord_2421550, baseEnd_2421550] using wordTrace_append hprefix tailTrace_2421550
  have hstable : (prefixWord ++ tailWord_2421550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421550).length < 2 ^ (prefixWord ++ tailWord_2421550).sum := by decide
  have hdescent : baseEnd_2421550 < baseStart_2421550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421576 : List Nat := [2, 1, 3, 1, 1, 3, 3, 1, 3, 4]
def baseStart_2421576 : Nat := 118140960795 + 2421576 * 2 ^ 59
def prefixEnd_2421576 : Nat := 4983230072969 + 3 ^ 40 * 2421576 * 2
def baseEnd_2421576 : Nat := 828954952928081870975587

theorem tailTrace_2421576 : CollatzResearch.WordTrace tailWord_2421576 prefixEnd_2421576 828954952928081870975587 := by
  unfold tailWord_2421576
  simp only [CollatzResearch.WordTrace]
  refine ⟨44161066337525599549870291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58881421783367466066493721 44161066337525599549870291)
  ·
    refine ⟨66241599506288399324805437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44161066337525599549870291 66241599506288399324805437)
    ·
      refine ⟨24840599814858149746802039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66241599506288399324805437 24840599814858149746802039)
      ·
        refine ⟨37260899722287224620203059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24840599814858149746802039 37260899722287224620203059)
        ·
          refine ⟨55891349583430836930304589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37260899722287224620203059 55891349583430836930304589)
          ·
            refine ⟨20959256093786563848864221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55891349583430836930304589 20959256093786563848864221)
            ·
              refine ⟨7859721035169961443324083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20959256093786563848864221 7859721035169961443324083)
              ·
                refine ⟨11789581552754942164986125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7859721035169961443324083 11789581552754942164986125)
                ·
                  refine ⟨4421093082283103311869797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11789581552754942164986125 4421093082283103311869797)
                  ·
                    refine ⟨828954952928081870975587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4421093082283103311869797 828954952928081870975587)
                    ·
                      rfl

theorem cell22_2421576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_2421576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2421576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2421576 prefixEnd_2421576 := by exact prefixLift 2421576
  have htrace : WordTrace (prefixWord ++ tailWord_2421576) baseStart_2421576 baseEnd_2421576 := by
    simpa [prefixWord, tailWord_2421576, baseEnd_2421576] using wordTrace_append hprefix tailTrace_2421576
  have hstable : (prefixWord ++ tailWord_2421576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421576).length < 2 ^ (prefixWord ++ tailWord_2421576).sum := by decide
  have hdescent : baseEnd_2421576 < baseStart_2421576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421745 : List Nat := [1, 2, 2, 2, 4, 1, 3, 2, 1, 4]
def baseStart_2421745 : Nat := 118140960795 + 2421745 * 2 ^ 59
def prefixEnd_2421745 : Nat := 4983230072969 + 3 ^ 40 * 2421745 * 2
def baseEnd_2421745 : Nat := 829012805081821763500069

theorem tailTrace_2421745 : CollatzResearch.WordTrace tailWord_2421745 prefixEnd_2421745 829012805081821763500069 := by
  unfold tailWord_2421745
  simp only [CollatzResearch.WordTrace]
  refine ⟨88328296611438940962642689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58885531074292627308428459 88328296611438940962642689)
  ·
    refine ⟨66246222458579205721982017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88328296611438940962642689 66246222458579205721982017)
    ·
      refine ⟨49684666843934404291486513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66246222458579205721982017 49684666843934404291486513)
      ·
        refine ⟨37263500132950803218614885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49684666843934404291486513 37263500132950803218614885)
        ·
          refine ⟨6986906274928275603490291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37263500132950803218614885 6986906274928275603490291)
          ·
            refine ⟨10480359412392413405235437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6986906274928275603490291 10480359412392413405235437)
            ·
              refine ⟨3930134779647155026963289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10480359412392413405235437 3930134779647155026963289)
              ·
                refine ⟨2947601084735366270222467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3930134779647155026963289 2947601084735366270222467)
                ·
                  refine ⟨4421401627103049405333701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2947601084735366270222467 4421401627103049405333701)
                  ·
                    refine ⟨829012805081821763500069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4421401627103049405333701 829012805081821763500069)
                    ·
                      rfl

theorem cell22_2421745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2, 1, 4].length) (baseStart_2421745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2421745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2421745 prefixEnd_2421745 := by exact prefixLift 2421745
  have htrace : WordTrace (prefixWord ++ tailWord_2421745) baseStart_2421745 baseEnd_2421745 := by
    simpa [prefixWord, tailWord_2421745, baseEnd_2421745] using wordTrace_append hprefix tailTrace_2421745
  have hstable : (prefixWord ++ tailWord_2421745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421745).length < 2 ^ (prefixWord ++ tailWord_2421745).sum := by decide
  have hdescent : baseEnd_2421745 < baseStart_2421745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421771 : List Nat := [1, 1, 1, 1, 6, 12]
def baseStart_2421771 : Nat := 118140960795 + 2421771 * 2 ^ 59
def prefixEnd_2421771 : Nat := 4983230072969 + 3 ^ 40 * 2421771 * 2
def baseEnd_2421771 : Nat := 10234835869298350152469

theorem tailTrace_2421771 : CollatzResearch.WordTrace tailWord_2421771 prefixEnd_2421771 10234835869298350152469 := by
  unfold tailWord_2421771
  simp only [CollatzResearch.WordTrace]
  refine ⟨88329244909344747403089167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58886163272896498268726111 88329244909344747403089167)
  ·
    refine ⟨132493867364017121104633751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88329244909344747403089167 132493867364017121104633751)
    ·
      refine ⟨198740801046025681656950627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132493867364017121104633751 198740801046025681656950627)
      ·
        refine ⟨298111201569038522485425941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198740801046025681656950627 298111201569038522485425941)
        ·
          refine ⟨13973962573548680741504341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 298111201569038522485425941 13973962573548680741504341)
          ·
            refine ⟨10234835869298350152469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 13973962573548680741504341 10234835869298350152469)
            ·
              rfl

theorem cell22_2421771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 12].length) (baseStart_2421771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2421771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2421771 prefixEnd_2421771 := by exact prefixLift 2421771
  have htrace : WordTrace (prefixWord ++ tailWord_2421771) baseStart_2421771 baseEnd_2421771 := by
    simpa [prefixWord, tailWord_2421771, baseEnd_2421771] using wordTrace_append hprefix tailTrace_2421771
  have hstable : (prefixWord ++ tailWord_2421771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421771).length < 2 ^ (prefixWord ++ tailWord_2421771).sum := by decide
  have hdescent : baseEnd_2421771 < baseStart_2421771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421792 : List Nat := [2, 1, 1, 7, 1, 1, 2, 1, 1, 5]
def baseStart_2421792 : Nat := 118140960795 + 2421792 * 2 ^ 59
def prefixEnd_2421792 : Nat := 4983230072969 + 3 ^ 40 * 2421792 * 2
def baseEnd_2421792 : Nat := 829028894142329307574925

theorem tailTrace_2421792 : CollatzResearch.WordTrace tailWord_2421792 prefixEnd_2421792 829028894142329307574925 := by
  unfold tailWord_2421792
  simp only [CollatzResearch.WordTrace]
  refine ⟨44165005421134333994801815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58886673894845778659735753 44165005421134333994801815)
  ·
    refine ⟨66247508131701500992202723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44165005421134333994801815 66247508131701500992202723)
    ·
      refine ⟨99371262197552251488304085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66247508131701500992202723 99371262197552251488304085)
      ·
        refine ⟨2329013957755130894257127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 99371262197552251488304085 2329013957755130894257127)
        ·
          refine ⟨3493520936632696341385691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2329013957755130894257127 3493520936632696341385691)
          ·
            refine ⟨5240281404949044512078537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3493520936632696341385691 5240281404949044512078537)
            ·
              refine ⟨3930211053711783384058903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5240281404949044512078537 3930211053711783384058903)
              ·
                refine ⟨5895316580567675076088355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3930211053711783384058903 5895316580567675076088355)
                ·
                  refine ⟨8842974870851512614132533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5895316580567675076088355 8842974870851512614132533)
                  ·
                    refine ⟨829028894142329307574925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8842974870851512614132533 829028894142329307574925)
                    ·
                      rfl

theorem cell22_2421792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 1, 5].length) (baseStart_2421792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2421792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2421792 prefixEnd_2421792 := by exact prefixLift 2421792
  have htrace : WordTrace (prefixWord ++ tailWord_2421792) baseStart_2421792 baseEnd_2421792 := by
    simpa [prefixWord, tailWord_2421792, baseEnd_2421792] using wordTrace_append hprefix tailTrace_2421792
  have hstable : (prefixWord ++ tailWord_2421792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421792).length < 2 ^ (prefixWord ++ tailWord_2421792).sum := by decide
  have hdescent : baseEnd_2421792 < baseStart_2421792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421833 : List Nat := [1, 2, 1, 1, 2, 2, 2, 6, 5]
def baseStart_2421833 : Nat := 118140960795 + 2421833 * 2 ^ 59
def prefixEnd_2421833 : Nat := 4983230072969 + 3 ^ 40 * 2421833 * 2
def baseEnd_2421833 : Nat := 276347643093406289099933

theorem tailTrace_2421833 : CollatzResearch.WordTrace tailWord_2421833 prefixEnd_2421833 276347643093406289099933 := by
  unfold tailWord_2421833
  simp only [CollatzResearch.WordTrace]
  refine ⟨88331506235120131991846153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58887670823413421327897435 88331506235120131991846153)
  ·
    refine ⟨66248629676340098993884615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88331506235120131991846153 66248629676340098993884615)
    ·
      refine ⟨99372944514510148490826923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66248629676340098993884615 99372944514510148490826923)
      ·
        refine ⟨149059416771765222736240385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99372944514510148490826923 149059416771765222736240385)
        ·
          refine ⟨111794562578823917052180289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149059416771765222736240385 111794562578823917052180289)
          ·
            refine ⟨83845921934117937789135217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111794562578823917052180289 83845921934117937789135217)
            ·
              refine ⟨62884441450588453341851413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83845921934117937789135217 62884441450588453341851413)
              ·
                refine ⟨2947708192996333750399285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 62884441450588453341851413 2947708192996333750399285)
                ·
                  refine ⟨276347643093406289099933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2947708192996333750399285 276347643093406289099933)
                  ·
                    rfl

theorem cell22_2421833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6, 5].length) (baseStart_2421833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2421833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2421833 prefixEnd_2421833 := by exact prefixLift 2421833
  have htrace : WordTrace (prefixWord ++ tailWord_2421833) baseStart_2421833 baseEnd_2421833 := by
    simpa [prefixWord, tailWord_2421833, baseEnd_2421833] using wordTrace_append hprefix tailTrace_2421833
  have hstable : (prefixWord ++ tailWord_2421833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421833).length < 2 ^ (prefixWord ++ tailWord_2421833).sum := by decide
  have hdescent : baseEnd_2421833 < baseStart_2421833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421837 : List Nat := [1, 6, 1, 1, 1, 2, 1, 3, 3, 3]
def baseStart_2421837 : Nat := 118140960795 + 2421837 * 2 ^ 59
def prefixEnd_2421837 : Nat := 4983230072969 + 3 ^ 40 * 2421837 * 2
def baseEnd_2421837 : Nat := 829044298561964190199787

theorem tailTrace_2421837 : CollatzResearch.WordTrace tailWord_2421837 prefixEnd_2421837 829044298561964190199787 := by
  unfold tailWord_2421837
  simp only [CollatzResearch.WordTrace]
  refine ⟨88331652127105640674991765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58887768084737093783327843 88331652127105640674991765)
  ·
    refine ⟨4140546193458076906640239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 88331652127105640674991765 4140546193458076906640239)
    ·
      refine ⟨6210819290187115359960359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4140546193458076906640239 6210819290187115359960359)
      ·
        refine ⟨9316228935280673039940539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6210819290187115359960359 9316228935280673039940539)
        ·
          refine ⟨13974343402921009559910809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9316228935280673039940539 13974343402921009559910809)
          ·
            refine ⟨10480757552190757169933107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13974343402921009559910809 10480757552190757169933107)
            ·
              refine ⟨15721136328286135754899661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10480757552190757169933107 15721136328286135754899661)
              ·
                refine ⟨5895426123107300908087373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15721136328286135754899661 5895426123107300908087373)
                ·
                  refine ⟨2210784796165237840532765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5895426123107300908087373 2210784796165237840532765)
                  ·
                    refine ⟨829044298561964190199787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2210784796165237840532765 829044298561964190199787)
                    ·
                      rfl

theorem cell22_2421837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_2421837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2421837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2421837 prefixEnd_2421837 := by exact prefixLift 2421837
  have htrace : WordTrace (prefixWord ++ tailWord_2421837) baseStart_2421837 baseEnd_2421837 := by
    simpa [prefixWord, tailWord_2421837, baseEnd_2421837] using wordTrace_append hprefix tailTrace_2421837
  have hstable : (prefixWord ++ tailWord_2421837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421837).length < 2 ^ (prefixWord ++ tailWord_2421837).sum := by decide
  have hdescent : baseEnd_2421837 < baseStart_2421837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421848 : List Nat := [2, 1, 2, 2, 1, 3, 1, 3, 2, 5]
def baseStart_2421848 : Nat := 118140960795 + 2421848 * 2 ^ 59
def prefixEnd_2421848 : Nat := 4983230072969 + 3 ^ 40 * 2421848 * 2
def baseEnd_2421848 : Nat := 829048064086763828174753

theorem tailTrace_2421848 : CollatzResearch.WordTrace tailWord_2421848 prefixEnd_2421848 829048064086763828174753 := by
  unfold tailWord_2421848
  simp only [CollatzResearch.WordTrace]
  refine ⟨44166026665032894776821099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58888035553377193035761465 44166026665032894776821099)
  ·
    refine ⟨66249039997549342165231649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44166026665032894776821099 66249039997549342165231649)
    ·
      refine ⟨49686779998162006623923737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66249039997549342165231649 49686779998162006623923737)
      ·
        refine ⟨37265084998621504967942803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49686779998162006623923737 37265084998621504967942803)
        ·
          refine ⟨55897627497932257451914205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37265084998621504967942803 55897627497932257451914205)
          ·
            refine ⟨20961610311724596544467827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55897627497932257451914205 20961610311724596544467827)
            ·
              refine ⟨31442415467586894816701741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20961610311724596544467827 31442415467586894816701741)
              ·
                refine ⟨11790905800345085556263153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31442415467586894816701741 11790905800345085556263153)
                ·
                  refine ⟨8843179350258814167197365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11790905800345085556263153 8843179350258814167197365)
                  ·
                    refine ⟨829048064086763828174753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8843179350258814167197365 829048064086763828174753)
                    ·
                      rfl

theorem cell22_2421848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_2421848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2421848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2421848 prefixEnd_2421848 := by exact prefixLift 2421848
  have htrace : WordTrace (prefixWord ++ tailWord_2421848) baseStart_2421848 baseEnd_2421848 := by
    simpa [prefixWord, tailWord_2421848, baseEnd_2421848] using wordTrace_append hprefix tailTrace_2421848
  have hstable : (prefixWord ++ tailWord_2421848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421848).length < 2 ^ (prefixWord ++ tailWord_2421848).sum := by decide
  have hdescent : baseEnd_2421848 < baseStart_2421848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421880 : List Nat := [2, 1, 2, 1, 1, 1, 6, 3, 1, 4]
def baseStart_2421880 : Nat := 118140960795 + 2421880 * 2 ^ 59
def prefixEnd_2421880 : Nat := 4983230072969 + 3 ^ 40 * 2421880 * 2
def baseEnd_2421880 : Nat := 829059018340726411374655

theorem tailTrace_2421880 : CollatzResearch.WordTrace tailWord_2421880 prefixEnd_2421880 829059018340726411374655 := by
  unfold tailWord_2421880
  simp only [CollatzResearch.WordTrace]
  refine ⟨44166610232974929509403547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58888813643966572679204729 44166610232974929509403547)
  ·
    refine ⟨66249915349462394264105321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44166610232974929509403547 66249915349462394264105321)
    ·
      refine ⟨49687436512096795698078991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66249915349462394264105321 49687436512096795698078991)
      ·
        refine ⟨74531154768145193547118487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49687436512096795698078991 74531154768145193547118487)
        ·
          refine ⟨111796732152217790320677731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74531154768145193547118487 111796732152217790320677731)
          ·
            refine ⟨167695098228326685481016597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111796732152217790320677731 167695098228326685481016597)
            ·
              refine ⟨7860707729452813381922653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 167695098228326685481016597 7860707729452813381922653)
              ·
                refine ⟨2947765398544805018220995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7860707729452813381922653 2947765398544805018220995)
                ·
                  refine ⟨4421648097817207527331493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2947765398544805018220995 4421648097817207527331493)
                  ·
                    refine ⟨829059018340726411374655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4421648097817207527331493 829059018340726411374655)
                    ·
                      rfl

theorem cell22_2421880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3, 1, 4].length) (baseStart_2421880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2421880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2421880 prefixEnd_2421880 := by exact prefixLift 2421880
  have htrace : WordTrace (prefixWord ++ tailWord_2421880) baseStart_2421880 baseEnd_2421880 := by
    simpa [prefixWord, tailWord_2421880, baseEnd_2421880] using wordTrace_append hprefix tailTrace_2421880
  have hstable : (prefixWord ++ tailWord_2421880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421880).length < 2 ^ (prefixWord ++ tailWord_2421880).sum := by decide
  have hdescent : baseEnd_2421880 < baseStart_2421880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421914 : List Nat := [3, 1, 1, 5, 1, 3, 1, 2, 1, 4]
def baseStart_2421914 : Nat := 118140960795 + 2421914 * 2 ^ 59
def prefixEnd_2421914 : Nat := 4983230072969 + 3 ^ 40 * 2421914 * 2
def baseEnd_2421914 : Nat := 829070657235561656024551

theorem tailTrace_2421914 : CollatzResearch.WordTrace tailWord_2421914 prefixEnd_2421914 829070657235561656024551 := by
  unfold tailWord_2421914
  simp only [CollatzResearch.WordTrace]
  refine ⟨22083615136956670706386199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58889640365217788550363197 22083615136956670706386199)
  ·
    refine ⟨33125422705435006059579299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22083615136956670706386199 33125422705435006059579299)
    ·
      refine ⟨49688134058152509089368949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33125422705435006059579299 49688134058152509089368949)
      ·
        refine ⟨4658262567951797727128339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49688134058152509089368949 4658262567951797727128339)
        ·
          refine ⟨6987393851927696590692509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4658262567951797727128339 6987393851927696590692509)
          ·
            refine ⟨2620272694472886221509691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6987393851927696590692509 2620272694472886221509691)
            ·
              refine ⟨3930409041709329332264537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2620272694472886221509691 3930409041709329332264537)
              ·
                refine ⟨2947806781281996999198403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3930409041709329332264537 2947806781281996999198403)
                ·
                  refine ⟨4421710171922995498797605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2947806781281996999198403 4421710171922995498797605)
                  ·
                    refine ⟨829070657235561656024551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4421710171922995498797605 829070657235561656024551)
                    ·
                      rfl

theorem cell22_2421914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 2, 1, 4].length) (baseStart_2421914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2421914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2421914 prefixEnd_2421914 := by exact prefixLift 2421914
  have htrace : WordTrace (prefixWord ++ tailWord_2421914) baseStart_2421914 baseEnd_2421914 := by
    simpa [prefixWord, tailWord_2421914, baseEnd_2421914] using wordTrace_append hprefix tailTrace_2421914
  have hstable : (prefixWord ++ tailWord_2421914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421914).length < 2 ^ (prefixWord ++ tailWord_2421914).sum := by decide
  have hdescent : baseEnd_2421914 < baseStart_2421914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421925 : List Nat := [1, 3, 1, 2, 1, 4, 1, 3, 2, 4]
def baseStart_2421925 : Nat := 118140960795 + 2421925 * 2 ^ 59
def prefixEnd_2421925 : Nat := 4983230072969 + 3 ^ 40 * 2421925 * 2
def baseEnd_2421925 : Nat := 829074422760361293999517

theorem tailTrace_2421925 : CollatzResearch.WordTrace tailWord_2421925 prefixEnd_2421925 829074422760361293999517 := by
  unfold tailWord_2421925
  simp only [CollatzResearch.WordTrace]
  refine ⟨88334861750786831704195229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58889907833857887802796819 88334861750786831704195229)
  ·
    refine ⟨33125573156545061889073211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88334861750786831704195229 33125573156545061889073211)
    ·
      refine ⟨49688359734817592833609817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33125573156545061889073211 49688359734817592833609817)
      ·
        refine ⟨37266269801113194625207363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49688359734817592833609817 37266269801113194625207363)
        ·
          refine ⟨55899404701669791937811045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37266269801113194625207363 55899404701669791937811045)
          ·
            refine ⟨10481138381563085988339571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55899404701669791937811045 10481138381563085988339571)
            ·
              refine ⟨15721707572344628982509357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10481138381563085988339571 15721707572344628982509357)
              ·
                refine ⟨5895640339629235868441009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15721707572344628982509357 5895640339629235868441009)
                ·
                  refine ⟨4421730254721926901330757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5895640339629235868441009 4421730254721926901330757)
                  ·
                    refine ⟨829074422760361293999517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4421730254721926901330757 829074422760361293999517)
                    ·
                      rfl

theorem cell22_2421925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2, 4].length) (baseStart_2421925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2421925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2421925 prefixEnd_2421925 := by exact prefixLift 2421925
  have htrace : WordTrace (prefixWord ++ tailWord_2421925) baseStart_2421925 baseEnd_2421925 := by
    simpa [prefixWord, tailWord_2421925, baseEnd_2421925] using wordTrace_append hprefix tailTrace_2421925
  have hstable : (prefixWord ++ tailWord_2421925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421925).length < 2 ^ (prefixWord ++ tailWord_2421925).sum := by decide
  have hdescent : baseEnd_2421925 < baseStart_2421925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421927 : List Nat := [1, 1, 6, 2, 1, 2, 1, 2, 1, 5]
def baseStart_2421927 : Nat := 118140960795 + 2421927 * 2 ^ 59
def prefixEnd_2421927 : Nat := 4983230072969 + 3 ^ 40 * 2421927 * 2
def baseEnd_2421927 : Nat := 829075107401233955449511

theorem tailTrace_2421927 : CollatzResearch.WordTrace tailWord_2421927 prefixEnd_2421927 829075107401233955449511 := by
  unfold tailWord_2421927
  simp only [CollatzResearch.WordTrace]
  refine ⟨88334934696779586045768035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58889956464519724030512023 88334934696779586045768035)
  ·
    refine ⟨132502402045169379068652053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88334934696779586045768035 132502402045169379068652053)
    ·
      refine ⟨6211050095867314643843065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 132502402045169379068652053 6211050095867314643843065)
      ·
        refine ⟨4658287571900485982882299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6211050095867314643843065 4658287571900485982882299)
        ·
          refine ⟨6987431357850728974323449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4658287571900485982882299 6987431357850728974323449)
          ·
            refine ⟨5240573518388046730742587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6987431357850728974323449 5240573518388046730742587)
            ·
              refine ⟨7860860277582070096113881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5240573518388046730742587 7860860277582070096113881)
              ·
                refine ⟨5895645208186552572085411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7860860277582070096113881 5895645208186552572085411)
                ·
                  refine ⟨8843467812279828858128117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5895645208186552572085411 8843467812279828858128117)
                  ·
                    refine ⟨829075107401233955449511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8843467812279828858128117 829075107401233955449511)
                    ·
                      rfl

theorem cell22_2421927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_2421927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2421927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2421927 prefixEnd_2421927 := by exact prefixLift 2421927
  have htrace : WordTrace (prefixWord ++ tailWord_2421927) baseStart_2421927 baseEnd_2421927 := by
    simpa [prefixWord, tailWord_2421927, baseEnd_2421927] using wordTrace_append hprefix tailTrace_2421927
  have hstable : (prefixWord ++ tailWord_2421927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421927).length < 2 ^ (prefixWord ++ tailWord_2421927).sum := by decide
  have hdescent : baseEnd_2421927 < baseStart_2421927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421970 : List Nat := [3, 2, 2, 2, 1, 1, 1, 2, 2, 6]
def baseStart_2421970 : Nat := 118140960795 + 2421970 * 2 ^ 59
def prefixEnd_2421970 : Nat := 4983230072969 + 3 ^ 40 * 2421970 * 2
def baseEnd_2421970 : Nat := 829089827179996176624379

theorem tailTrace_2421970 : CollatzResearch.WordTrace tailWord_2421970 prefixEnd_2421970 829089827179996176624379 := by
  unfold tailWord_2421970
  simp only [CollatzResearch.WordTrace]
  refine ⟨22084125758905951097395841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58891002023749202926388909 22084125758905951097395841)
  ·
    refine ⟨16563094319179463323046881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22084125758905951097395841 16563094319179463323046881)
    ·
      refine ⟨12422320739384597492285161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16563094319179463323046881 12422320739384597492285161)
      ·
        refine ⟨9316740554538448119213871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12422320739384597492285161 9316740554538448119213871)
        ·
          refine ⟨13975110831807672178820807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9316740554538448119213871 13975110831807672178820807)
          ·
            refine ⟨20962666247711508268231211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13975110831807672178820807 20962666247711508268231211)
            ·
              refine ⟨31443999371567262402346817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20962666247711508268231211 31443999371567262402346817)
              ·
                refine ⟨23582999528675446801760113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31443999371567262402346817 23582999528675446801760113)
                ·
                  refine ⟨17687249646506585101320085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23582999528675446801760113 17687249646506585101320085)
                  ·
                    refine ⟨829089827179996176624379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17687249646506585101320085 829089827179996176624379)
                    ·
                      rfl

theorem cell22_2421970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_2421970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2421970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2421970 prefixEnd_2421970 := by exact prefixLift 2421970
  have htrace : WordTrace (prefixWord ++ tailWord_2421970) baseStart_2421970 baseEnd_2421970 := by
    simpa [prefixWord, tailWord_2421970, baseEnd_2421970] using wordTrace_append hprefix tailTrace_2421970
  have hstable : (prefixWord ++ tailWord_2421970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421970).length < 2 ^ (prefixWord ++ tailWord_2421970).sum := by decide
  have hdescent : baseEnd_2421970 < baseStart_2421970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422002 : List Nat := [3, 2, 1, 3, 3, 1, 1, 1, 7]
def baseStart_2422002 : Nat := 118140960795 + 2422002 * 2 ^ 59
def prefixEnd_2422002 : Nat := 4983230072969 + 3 ^ 40 * 2422002 * 2
def baseEnd_2422002 : Nat := 276366927144652919941427

theorem tailTrace_2422002 : CollatzResearch.WordTrace tailWord_2422002 prefixEnd_2422002 276366927144652919941427 := by
  unfold tailWord_2422002
  simp only [CollatzResearch.WordTrace]
  refine ⟨22084417542876968463687065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58891780114338582569832173 22084417542876968463687065)
  ·
    refine ⟨16563313157157726347765299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22084417542876968463687065 16563313157157726347765299)
    ·
      refine ⟨24844969735736589521647949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16563313157157726347765299 24844969735736589521647949)
      ·
        refine ⟨9316863650901221070617981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24844969735736589521647949 9316863650901221070617981)
        ·
          refine ⟨3493823869087957901481743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9316863650901221070617981 3493823869087957901481743)
          ·
            refine ⟨5240735803631936852222615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3493823869087957901481743 5240735803631936852222615)
            ·
              refine ⟨7861103705447905278333923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5240735803631936852222615 7861103705447905278333923)
              ·
                refine ⟨11791655558171857917500885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7861103705447905278333923 11791655558171857917500885)
                ·
                  refine ⟨276366927144652919941427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11791655558171857917500885 276366927144652919941427)
                  ·
                    rfl

theorem cell22_2422002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_2422002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2422002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2422002 prefixEnd_2422002 := by exact prefixLift 2422002
  have htrace : WordTrace (prefixWord ++ tailWord_2422002) baseStart_2422002 baseEnd_2422002 := by
    simpa [prefixWord, tailWord_2422002, baseEnd_2422002] using wordTrace_append hprefix tailTrace_2422002
  have hstable : (prefixWord ++ tailWord_2422002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422002).length < 2 ^ (prefixWord ++ tailWord_2422002).sum := by decide
  have hdescent : baseEnd_2422002 < baseStart_2422002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422064 : List Nat := [2, 1, 1, 1, 2, 2, 7, 2, 4]
def baseStart_2422064 : Nat := 118140960795 + 2422064 * 2 ^ 59
def prefixEnd_2422064 : Nat := 4983230072969 + 3 ^ 40 * 2422064 * 2
def baseEnd_2422064 : Nat := 276374001767003754924697

theorem tailTrace_2422064 : CollatzResearch.WordTrace tailWord_2422064 prefixEnd_2422064 276374001767003754924697 := by
  unfold tailWord_2422064
  simp only [CollatzResearch.WordTrace]
  refine ⟨44169965748641629221752623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58893287664855505629003497 44169965748641629221752623)
  ·
    refine ⟨66254948622962443832628935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44169965748641629221752623 66254948622962443832628935)
    ·
      refine ⟨99382422934443665748943403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66254948622962443832628935 99382422934443665748943403)
      ·
        refine ⟨149073634401665498623415105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99382422934443665748943403 149073634401665498623415105)
        ·
          refine ⟨111805225801249123967561329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149073634401665498623415105 111805225801249123967561329)
          ·
            refine ⟨83853919350936842975670997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111805225801249123967561329 83853919350936842975670997)
            ·
              refine ⟨1965326234787582257242289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 83853919350936842975670997 1965326234787582257242289)
              ·
                refine ⟨1473994676090686692931717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1965326234787582257242289 1473994676090686692931717)
                ·
                  refine ⟨276374001767003754924697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1473994676090686692931717 276374001767003754924697)
                  ·
                    rfl

theorem cell22_2422064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 2, 4].length) (baseStart_2422064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2422064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2422064 prefixEnd_2422064 := by exact prefixLift 2422064
  have htrace : WordTrace (prefixWord ++ tailWord_2422064) baseStart_2422064 baseEnd_2422064 := by
    simpa [prefixWord, tailWord_2422064, baseEnd_2422064] using wordTrace_append hprefix tailTrace_2422064
  have hstable : (prefixWord ++ tailWord_2422064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422064).length < 2 ^ (prefixWord ++ tailWord_2422064).sum := by decide
  have hdescent : baseEnd_2422064 < baseStart_2422064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422070 : List Nat := [5, 1, 2, 3, 2, 1, 2, 1, 5]
def baseStart_2422070 : Nat := 118140960795 + 2422070 * 2 ^ 59
def prefixEnd_2422070 : Nat := 4983230072969 + 3 ^ 40 * 2422070 * 2
def baseEnd_2422070 : Nat := 276374686407876416374691

theorem tailTrace_2422070 : CollatzResearch.WordTrace tailWord_2422070 prefixEnd_2422070 276374686407876416374691 := by
  unfold tailWord_2422070
  simp only [CollatzResearch.WordTrace]
  refine ⟨5521259395953845091763979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58893433556841014312149109 5521259395953845091763979)
  ·
    refine ⟨8281889093930767637645969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5521259395953845091763979 8281889093930767637645969)
    ·
      refine ⟨6211416820448075728234477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8281889093930767637645969 6211416820448075728234477)
      ·
        refine ⟨2329281307668028398087929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6211416820448075728234477 2329281307668028398087929)
        ·
          refine ⟨1746960980751021298565947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2329281307668028398087929 1746960980751021298565947)
          ·
            refine ⟨2620441471126531947848921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1746960980751021298565947 2620441471126531947848921)
            ·
              refine ⟨1965331103344898960886691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2620441471126531947848921 1965331103344898960886691)
              ·
                refine ⟨2947996655017348441330037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1965331103344898960886691 2947996655017348441330037)
                ·
                  refine ⟨276374686407876416374691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2947996655017348441330037 276374686407876416374691)
                  ·
                    rfl

theorem cell22_2422070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_2422070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2422070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2422070 prefixEnd_2422070 := by exact prefixLift 2422070
  have htrace : WordTrace (prefixWord ++ tailWord_2422070) baseStart_2422070 baseEnd_2422070 := by
    simpa [prefixWord, tailWord_2422070, baseEnd_2422070] using wordTrace_append hprefix tailTrace_2422070
  have hstable : (prefixWord ++ tailWord_2422070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422070).length < 2 ^ (prefixWord ++ tailWord_2422070).sum := by decide
  have hdescent : baseEnd_2422070 < baseStart_2422070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422079 : List Nat := [1, 1, 2, 2, 4, 3, 1, 3, 2, 3]
def baseStart_2422079 : Nat := 118140960795 + 2422079 * 2 ^ 59
def prefixEnd_2422079 : Nat := 4983230072969 + 3 ^ 40 * 2422079 * 2
def baseEnd_2422079 : Nat := 829127140107556225649045

theorem tailTrace_2422079 : CollatzResearch.WordTrace tailWord_2422079 prefixEnd_2422079 829127140107556225649045 := by
  unfold tailWord_2422079
  simp only [CollatzResearch.WordTrace]
  refine ⟨88340478592228916005301291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58893652394819277336867527 88340478592228916005301291)
  ·
    refine ⟨132510717888343374007951937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88340478592228916005301291 132510717888343374007951937)
    ·
      refine ⟨99383038416257530505963953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132510717888343374007951937 99383038416257530505963953)
      ·
        refine ⟨74537278812193147879472965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99383038416257530505963953 74537278812193147879472965)
        ·
          refine ⟨13975739777286215227401181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74537278812193147879472965 13975739777286215227401181)
          ·
            refine ⟨5240902416482330710275443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13975739777286215227401181 5240902416482330710275443)
            ·
              refine ⟨7861353624723496065413165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5240902416482330710275443 7861353624723496065413165)
              ·
                refine ⟨2948007609271311024529937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7861353624723496065413165 2948007609271311024529937)
                ·
                  refine ⟨2211005706953483268397453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2948007609271311024529937 2211005706953483268397453)
                  ·
                    refine ⟨829127140107556225649045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2211005706953483268397453 829127140107556225649045)
                    ·
                      rfl

theorem cell22_2422079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3, 2, 3].length) (baseStart_2422079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2422079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2422079 prefixEnd_2422079 := by exact prefixLift 2422079
  have htrace : WordTrace (prefixWord ++ tailWord_2422079) baseStart_2422079 baseEnd_2422079 := by
    simpa [prefixWord, tailWord_2422079, baseEnd_2422079] using wordTrace_append hprefix tailTrace_2422079
  have hstable : (prefixWord ++ tailWord_2422079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422079).length < 2 ^ (prefixWord ++ tailWord_2422079).sum := by decide
  have hdescent : baseEnd_2422079 < baseStart_2422079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422090 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 2, 7]
def baseStart_2422090 : Nat := 118140960795 + 2422090 * 2 ^ 59
def prefixEnd_2422090 : Nat := 4983230072969 + 3 ^ 40 * 2422090 * 2
def baseEnd_2422090 : Nat := 829130905632355863624011

theorem tailTrace_2422090 : CollatzResearch.WordTrace tailWord_2422090 prefixEnd_2422090 829130905632355863624011 := by
  unfold tailWord_2422090
  simp only [CollatzResearch.WordTrace]
  refine ⟨22085219948797266220987931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58893919863459376589301149 22085219948797266220987931)
  ·
    refine ⟨33127829923195899331481897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22085219948797266220987931 33127829923195899331481897)
    ·
      refine ⟨24845872442396924498611423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33127829923195899331481897 24845872442396924498611423)
      ·
        refine ⟨37268808663595386747917135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24845872442396924498611423 37268808663595386747917135)
        ·
          refine ⟨55903212995393080121875703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37268808663595386747917135 55903212995393080121875703)
          ·
            refine ⟨83854819493089620182813555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55903212995393080121875703 83854819493089620182813555)
            ·
              refine ⟨125782229239634430274220333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83854819493089620182813555 125782229239634430274220333)
              ·
                refine ⟨47168335964862911352832625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125782229239634430274220333 47168335964862911352832625)
                ·
                  refine ⟨35376251973647183514624469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47168335964862911352832625 35376251973647183514624469)
                  ·
                    refine ⟨829130905632355863624011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35376251973647183514624469 829130905632355863624011)
                    ·
                      rfl

theorem cell22_2422090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_2422090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2422090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2422090 prefixEnd_2422090 := by exact prefixLift 2422090
  have htrace : WordTrace (prefixWord ++ tailWord_2422090) baseStart_2422090 baseEnd_2422090 := by
    simpa [prefixWord, tailWord_2422090, baseEnd_2422090] using wordTrace_append hprefix tailTrace_2422090
  have hstable : (prefixWord ++ tailWord_2422090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422090).length < 2 ^ (prefixWord ++ tailWord_2422090).sum := by decide
  have hdescent : baseEnd_2422090 < baseStart_2422090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422109 : List Nat := [1, 4, 5, 1, 11]
def baseStart_2422109 : Nat := 118140960795 + 2422109 * 2 ^ 59
def prefixEnd_2422109 : Nat := 4983230072969 + 3 ^ 40 * 2422109 * 2
def baseEnd_2422109 : Nat := 3412088105846280441971

theorem tailTrace_2422109 : CollatzResearch.WordTrace tailWord_2422109 prefixEnd_2422109 3412088105846280441971 := by
  unfold tailWord_2422109
  simp only [CollatzResearch.WordTrace]
  refine ⟨88341572782120231128893381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58894381854746820752595587 88341572782120231128893381)
  ·
    refine ⟨16564044896647543336667509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88341572782120231128893381 16564044896647543336667509)
    ·
      refine ⟨1552879209060707187812579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16564044896647543336667509 1552879209060707187812579)
      ·
        refine ⟨2329318813591060781718869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1552879209060707187812579 2329318813591060781718869)
        ·
          refine ⟨3412088105846280441971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2329318813591060781718869 3412088105846280441971)
          ·
            rfl

theorem cell22_2422109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 11].length) (baseStart_2422109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2422109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2422109 prefixEnd_2422109 := by exact prefixLift 2422109
  have htrace : WordTrace (prefixWord ++ tailWord_2422109) baseStart_2422109 baseEnd_2422109 := by
    simpa [prefixWord, tailWord_2422109, baseEnd_2422109] using wordTrace_append hprefix tailTrace_2422109
  have hstable : (prefixWord ++ tailWord_2422109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422109).length < 2 ^ (prefixWord ++ tailWord_2422109).sum := by decide
  have hdescent : baseEnd_2422109 < baseStart_2422109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422126 : List Nat := [4, 1, 2, 4, 1, 2, 1, 7]
def baseStart_2422126 : Nat := 118140960795 + 2422126 * 2 ^ 59
def prefixEnd_2422126 : Nat := 4983230072969 + 3 ^ 40 * 2422126 * 2
def baseEnd_2422126 : Nat := 92127025463118196635989

theorem tailTrace_2422126 : CollatzResearch.WordTrace tailWord_2422126 prefixEnd_2422126 92127025463118196635989 := by
  unfold tailWord_2422126
  simp only [CollatzResearch.WordTrace]
  refine ⟨11042774102882330379032779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58894795215372428688174821 11042774102882330379032779)
  ·
    refine ⟨16564161154323495568549169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11042774102882330379032779 16564161154323495568549169)
    ·
      refine ⟨12423120865742621676411877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16564161154323495568549169 12423120865742621676411877)
      ·
        refine ⟨2329335162326741564327227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12423120865742621676411877 2329335162326741564327227)
        ·
          refine ⟨3494002743490112346490841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2329335162326741564327227 3494002743490112346490841)
          ·
            refine ⟨2620502057617584259868131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3494002743490112346490841 2620502057617584259868131)
            ·
              refine ⟨3930753086426376389802197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2620502057617584259868131 3930753086426376389802197)
              ·
                refine ⟨92127025463118196635989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3930753086426376389802197 92127025463118196635989)
                ·
                  rfl

theorem cell22_2422126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 7].length) (baseStart_2422126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2422126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2422126 prefixEnd_2422126 := by exact prefixLift 2422126
  have htrace : WordTrace (prefixWord ++ tailWord_2422126) baseStart_2422126 baseEnd_2422126 := by
    simpa [prefixWord, tailWord_2422126, baseEnd_2422126] using wordTrace_append hprefix tailTrace_2422126
  have hstable : (prefixWord ++ tailWord_2422126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422126).length < 2 ^ (prefixWord ++ tailWord_2422126).sum := by decide
  have hdescent : baseEnd_2422126 < baseStart_2422126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422137 : List Nat := [1, 2, 1, 3, 2, 1, 4, 3, 5]
def baseStart_2422137 : Nat := 118140960795 + 2422137 * 2 ^ 59
def prefixEnd_2422137 : Nat := 4983230072969 + 3 ^ 40 * 2422137 * 2
def baseEnd_2422137 : Nat := 276382331564287802566289

theorem tailTrace_2422137 : CollatzResearch.WordTrace tailWord_2422137 prefixEnd_2422137 276382331564287802566289 := by
  unfold tailWord_2422137
  simp only [CollatzResearch.WordTrace]
  refine ⟨88342594026018791910912665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58895062684012527940608443 88342594026018791910912665)
  ·
    refine ⟨66256945519514093933184499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88342594026018791910912665 66256945519514093933184499)
    ·
      refine ⟨99385418279271140899776749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66256945519514093933184499 99385418279271140899776749)
      ·
        refine ⟨37269531854726677837416281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99385418279271140899776749 37269531854726677837416281)
        ·
          refine ⟨27952148891045008378062211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37269531854726677837416281 27952148891045008378062211)
          ·
            refine ⟨41928223336567512567093317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27952148891045008378062211 41928223336567512567093317)
            ·
              refine ⟨7861541875606408606329997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41928223336567512567093317 7861541875606408606329997)
              ·
                refine ⟨2948078203352403227373749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7861541875606408606329997 2948078203352403227373749)
                ·
                  refine ⟨276382331564287802566289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2948078203352403227373749 276382331564287802566289)
                  ·
                    rfl

theorem cell22_2422137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3, 5].length) (baseStart_2422137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2422137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2422137 prefixEnd_2422137 := by exact prefixLift 2422137
  have htrace : WordTrace (prefixWord ++ tailWord_2422137) baseStart_2422137 baseEnd_2422137 := by
    simpa [prefixWord, tailWord_2422137, baseEnd_2422137] using wordTrace_append hprefix tailTrace_2422137
  have hstable : (prefixWord ++ tailWord_2422137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422137).length < 2 ^ (prefixWord ++ tailWord_2422137).sum := by decide
  have hdescent : baseEnd_2422137 < baseStart_2422137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422201 : List Nat := [1, 2, 1, 4, 4, 1, 2, 2, 1, 4]
def baseStart_2422201 : Nat := 118140960795 + 2422201 * 2 ^ 59
def prefixEnd_2422201 : Nat := 4983230072969 + 3 ^ 40 * 2422201 * 2
def baseEnd_2422201 : Nat := 829168903200788574098671

theorem tailTrace_2422201 : CollatzResearch.WordTrace tailWord_2422201 prefixEnd_2422201 829168903200788574098671 := by
  unfold tailWord_2422201
  simp only [CollatzResearch.WordTrace]
  refine ⟨88344928297786930841242457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58896618865191287227494971 88344928297786930841242457)
  ·
    refine ⟨66258696223340198130931843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88344928297786930841242457 66258696223340198130931843)
    ·
      refine ⟨99388044335010297196397765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66258696223340198130931843 99388044335010297196397765)
      ·
        refine ⟨18635258312814430724324581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99388044335010297196397765 18635258312814430724324581)
        ·
          refine ⟨3494110933652705760810859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18635258312814430724324581 3494110933652705760810859)
          ·
            refine ⟨5241166400479058641216289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3494110933652705760810859 5241166400479058641216289)
            ·
              refine ⟨3930874800359293980912217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5241166400479058641216289 3930874800359293980912217)
              ·
                refine ⟨2948156100269470485684163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3930874800359293980912217 2948156100269470485684163)
                ·
                  refine ⟨4422234150404205728526245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2948156100269470485684163 4422234150404205728526245)
                  ·
                    refine ⟨829168903200788574098671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4422234150404205728526245 829168903200788574098671)
                    ·
                      rfl

theorem cell22_2422201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2, 1, 4].length) (baseStart_2422201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2422201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2422201 prefixEnd_2422201 := by exact prefixLift 2422201
  have htrace : WordTrace (prefixWord ++ tailWord_2422201) baseStart_2422201 baseEnd_2422201 := by
    simpa [prefixWord, tailWord_2422201, baseEnd_2422201] using wordTrace_append hprefix tailTrace_2422201
  have hstable : (prefixWord ++ tailWord_2422201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422201).length < 2 ^ (prefixWord ++ tailWord_2422201).sum := by decide
  have hdescent : baseEnd_2422201 < baseStart_2422201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422229 : List Nat := [1, 3, 2, 3, 1, 1, 3, 2, 2, 4]
def baseStart_2422229 : Nat := 118140960795 + 2422229 * 2 ^ 59
def prefixEnd_2422229 : Nat := 4983230072969 + 3 ^ 40 * 2422229 * 2
def baseEnd_2422229 : Nat := 829178488173005834398585

theorem tailTrace_2422229 : CollatzResearch.WordTrace tailWord_2422229 prefixEnd_2422229 829178488173005834398585 := by
  unfold tailWord_2422229
  simp only [CollatzResearch.WordTrace]
  refine ⟨88345949541685491623261741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58897299694456994415507827 88345949541685491623261741)
  ·
    refine ⟨33129731078132059358723153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88345949541685491623261741 33129731078132059358723153)
    ·
      refine ⟨24847298308599044519042365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33129731078132059358723153 24847298308599044519042365)
      ·
        refine ⟨9317736865724641694640887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24847298308599044519042365 9317736865724641694640887)
        ·
          refine ⟨13976605298586962541961331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9317736865724641694640887 13976605298586962541961331)
          ·
            refine ⟨20964907947880443812941997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13976605298586962541961331 20964907947880443812941997)
            ·
              refine ⟨7861840480455166429853249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20964907947880443812941997 7861840480455166429853249)
              ·
                refine ⟨5896380360341374822389937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7861840480455166429853249 5896380360341374822389937)
                ·
                  refine ⟨4422285270256031116792453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5896380360341374822389937 4422285270256031116792453)
                  ·
                    refine ⟨829178488173005834398585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4422285270256031116792453 829178488173005834398585)
                    ·
                      rfl

theorem cell22_2422229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_2422229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2422229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2422229 prefixEnd_2422229 := by exact prefixLift 2422229
  have htrace : WordTrace (prefixWord ++ tailWord_2422229) baseStart_2422229 baseEnd_2422229 := by
    simpa [prefixWord, tailWord_2422229, baseEnd_2422229] using wordTrace_append hprefix tailTrace_2422229
  have hstable : (prefixWord ++ tailWord_2422229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422229).length < 2 ^ (prefixWord ++ tailWord_2422229).sum := by decide
  have hdescent : baseEnd_2422229 < baseStart_2422229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422278 : List Nat := [6, 2, 1, 1, 2, 10]
def baseStart_2422278 : Nat := 118140960795 + 2422278 * 2 ^ 59
def prefixEnd_2422278 : Nat := 4983230072969 + 3 ^ 40 * 2422278 * 2
def baseEnd_2422278 : Nat := 10236978541659086912635

theorem tailTrace_2422278 : CollatzResearch.WordTrace tailWord_2422278 prefixEnd_2422278 10236978541659086912635 := by
  unfold tailWord_2422278
  simp only [CollatzResearch.WordTrace]
  refine ⟨2760866772453374155993609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 58898491145671981994530325 2760866772453374155993609)
  ·
    refine ⟨2070650079340030616995207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2760866772453374155993609 2070650079340030616995207)
    ·
      refine ⟨3105975119010045925492811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2070650079340030616995207 3105975119010045925492811)
      ·
        refine ⟨4658962678515068888239217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3105975119010045925492811 4658962678515068888239217)
        ·
          refine ⟨3494222008886301666179413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4658962678515068888239217 3494222008886301666179413)
          ·
            refine ⟨10236978541659086912635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3494222008886301666179413 10236978541659086912635)
            ·
              rfl

theorem cell22_2422278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 10].length) (baseStart_2422278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2422278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2422278 prefixEnd_2422278 := by exact prefixLift 2422278
  have htrace : WordTrace (prefixWord ++ tailWord_2422278) baseStart_2422278 baseEnd_2422278 := by
    simpa [prefixWord, tailWord_2422278, baseEnd_2422278] using wordTrace_append hprefix tailTrace_2422278
  have hstable : (prefixWord ++ tailWord_2422278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422278).length < 2 ^ (prefixWord ++ tailWord_2422278).sum := by decide
  have hdescent : baseEnd_2422278 < baseStart_2422278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422289 : List Nat := [1, 2, 2, 1, 1, 2, 6, 2, 5]
def baseStart_2422289 : Nat := 118140960795 + 2422289 * 2 ^ 59
def prefixEnd_2422289 : Nat := 4983230072969 + 3 ^ 40 * 2422289 * 2
def baseEnd_2422289 : Nat := 276399675799728559299467

theorem tailTrace_2422289 : CollatzResearch.WordTrace tailWord_2422289 prefixEnd_2422289 276399675799728559299467 := by
  unfold tailWord_2422289
  simp only [CollatzResearch.WordTrace]
  refine ⟨88348137921468121870445921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58898758614312081246963947 88348137921468121870445921)
  ·
    refine ⟨66261103441101091402834441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88348137921468121870445921 66261103441101091402834441)
    ·
      refine ⟨49695827580825818552125831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66261103441101091402834441 49695827580825818552125831)
      ·
        refine ⟨74543741371238727828188747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49695827580825818552125831 74543741371238727828188747)
        ·
          refine ⟨111815612056858091742283121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74543741371238727828188747 111815612056858091742283121)
          ·
            refine ⟨83861709042643568806712341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111815612056858091742283121 83861709042643568806712341)
            ·
              refine ⟨3931017611373917287814641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 83861709042643568806712341 3931017611373917287814641)
              ·
                refine ⟨2948263208530437965860981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3931017611373917287814641 2948263208530437965860981)
                ·
                  refine ⟨276399675799728559299467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2948263208530437965860981 276399675799728559299467)
                  ·
                    rfl

theorem cell22_2422289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2, 5].length) (baseStart_2422289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2422289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2422289 prefixEnd_2422289 := by exact prefixLift 2422289
  have htrace : WordTrace (prefixWord ++ tailWord_2422289) baseStart_2422289 baseEnd_2422289 := by
    simpa [prefixWord, tailWord_2422289, baseEnd_2422289] using wordTrace_append hprefix tailTrace_2422289
  have hstable : (prefixWord ++ tailWord_2422289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422289).length < 2 ^ (prefixWord ++ tailWord_2422289).sum := by decide
  have hdescent : baseEnd_2422289 < baseStart_2422289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422293 : List Nat := [1, 3, 2, 1, 3, 3, 1, 4, 1, 3]
def baseStart_2422293 : Nat := 118140960795 + 2422293 * 2 ^ 59
def prefixEnd_2422293 : Nat := 4983230072969 + 3 ^ 40 * 2422293 * 2
def baseEnd_2422293 : Nat := 829200396680931000798389

theorem tailTrace_2422293 : CollatzResearch.WordTrace tailWord_2422293 prefixEnd_2422293 829200396680931000798389 := by
  unfold tailWord_2422293
  simp only [CollatzResearch.WordTrace]
  refine ⟨88348283813453630553591533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58898855875635753702394355 88348283813453630553591533)
  ·
    refine ⟨33130606430045111457596825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88348283813453630553591533 33130606430045111457596825)
    ·
      refine ⟨24847954822533833593197619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33130606430045111457596825 24847954822533833593197619)
      ·
        refine ⟨37271932233800750389796429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24847954822533833593197619 37271932233800750389796429)
        ·
          refine ⟨13976974587675281396173661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37271932233800750389796429 13976974587675281396173661)
          ·
            refine ⟨5241365470378230523565123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13976974587675281396173661 5241365470378230523565123)
            ·
              refine ⟨7862048205567345785347685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5241365470378230523565123 7862048205567345785347685)
              ·
                refine ⟨1474134038543877334752691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7862048205567345785347685 1474134038543877334752691)
                ·
                  refine ⟨2211201057815816002129037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1474134038543877334752691 2211201057815816002129037)
                  ·
                    refine ⟨829200396680931000798389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2211201057815816002129037 829200396680931000798389)
                    ·
                      rfl

theorem cell22_2422293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 4, 1, 3].length) (baseStart_2422293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2422293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2422293 prefixEnd_2422293 := by exact prefixLift 2422293
  have htrace : WordTrace (prefixWord ++ tailWord_2422293) baseStart_2422293 baseEnd_2422293 := by
    simpa [prefixWord, tailWord_2422293, baseEnd_2422293] using wordTrace_append hprefix tailTrace_2422293
  have hstable : (prefixWord ++ tailWord_2422293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422293).length < 2 ^ (prefixWord ++ tailWord_2422293).sum := by decide
  have hdescent : baseEnd_2422293 < baseStart_2422293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422304 : List Nat := [2, 1, 1, 6, 1, 1, 1, 1, 1, 7]
def baseStart_2422304 : Nat := 118140960795 + 2422304 * 2 ^ 59
def prefixEnd_2422304 : Nat := 4983230072969 + 3 ^ 40 * 2422304 * 2
def baseEnd_2422304 : Nat := 829204162205730638773355

theorem tailTrace_2422304 : CollatzResearch.WordTrace tailWord_2422304 prefixEnd_2422304 829204162205730638773355 := by
  unfold tailWord_2422304
  simp only [CollatzResearch.WordTrace]
  refine ⟨44174342508206889716120983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58899123344275852954827977 44174342508206889716120983)
  ·
    refine ⟨66261513762310334574181475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44174342508206889716120983 66261513762310334574181475)
    ·
      refine ⟨99392270643465501861272213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66261513762310334574181475 99392270643465501861272213)
      ·
        refine ⟨4659012686412445399747135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 99392270643465501861272213 4659012686412445399747135)
        ·
          refine ⟨6988519029618668099620703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4659012686412445399747135 6988519029618668099620703)
          ·
            refine ⟨10482778544428002149431055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6988519029618668099620703 10482778544428002149431055)
            ·
              refine ⟨15724167816642003224146583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10482778544428002149431055 15724167816642003224146583)
              ·
                refine ⟨23586251724963004836219875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15724167816642003224146583 23586251724963004836219875)
                ·
                  refine ⟨35379377587444507254329813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23586251724963004836219875 35379377587444507254329813)
                  ·
                    refine ⟨829204162205730638773355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35379377587444507254329813 829204162205730638773355)
                    ·
                      rfl

theorem cell22_2422304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 1, 7].length) (baseStart_2422304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2422304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2422304 prefixEnd_2422304 := by exact prefixLift 2422304
  have htrace : WordTrace (prefixWord ++ tailWord_2422304) baseStart_2422304 baseEnd_2422304 := by
    simpa [prefixWord, tailWord_2422304, baseEnd_2422304] using wordTrace_append hprefix tailTrace_2422304
  have hstable : (prefixWord ++ tailWord_2422304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422304).length < 2 ^ (prefixWord ++ tailWord_2422304).sum := by decide
  have hdescent : baseEnd_2422304 < baseStart_2422304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422445 : List Nat := [1, 5, 2, 1, 1, 1, 2, 5, 1, 3]
def baseStart_2422445 : Nat := 118140960795 + 2422445 * 2 ^ 59
def prefixEnd_2422445 : Nat := 4983230072969 + 3 ^ 40 * 2422445 * 2
def baseEnd_2422445 : Nat := 829252429387253270997923

theorem tailTrace_2422445 : CollatzResearch.WordTrace tailWord_2422445 prefixEnd_2422445 829252429387253270997923 := by
  unfold tailWord_2422445
  simp only [CollatzResearch.WordTrace]
  refine ⟨88353827708902960513124789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58902551805935307008749859 88353827708902960513124789)
  ·
    refine ⟨8283171347709652548105449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88353827708902960513124789 8283171347709652548105449)
    ·
      refine ⟨6212378510782239411079087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8283171347709652548105449 6212378510782239411079087)
      ·
        refine ⟨9318567766173359116618631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6212378510782239411079087 9318567766173359116618631)
        ·
          refine ⟨13977851649260038674927947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9318567766173359116618631 13977851649260038674927947)
          ·
            refine ⟨20966777473890058012391921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13977851649260038674927947 20966777473890058012391921)
            ·
              refine ⟨15725083105417543509293941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20966777473890058012391921 15725083105417543509293941)
              ·
                refine ⟨1474226541132894703996307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15725083105417543509293941 1474226541132894703996307)
                ·
                  refine ⟨2211339811699342055994461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1474226541132894703996307 2211339811699342055994461)
                  ·
                    refine ⟨829252429387253270997923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2211339811699342055994461 829252429387253270997923)
                    ·
                      rfl

theorem cell22_2422445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_2422445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2422445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2422445 prefixEnd_2422445 := by exact prefixLift 2422445
  have htrace : WordTrace (prefixWord ++ tailWord_2422445) baseStart_2422445 baseEnd_2422445 := by
    simpa [prefixWord, tailWord_2422445, baseEnd_2422445] using wordTrace_append hprefix tailTrace_2422445
  have hstable : (prefixWord ++ tailWord_2422445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422445).length < 2 ^ (prefixWord ++ tailWord_2422445).sum := by decide
  have hdescent : baseEnd_2422445 < baseStart_2422445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422462 : List Nat := [4, 2, 1, 1, 2, 2, 4, 2, 1, 3]
def baseStart_2422462 : Nat := 118140960795 + 2422462 * 2 ^ 59
def prefixEnd_2422462 : Nat := 4983230072969 + 3 ^ 40 * 2422462 * 2
def baseEnd_2422462 : Nat := 829258248834670893322871

theorem tailTrace_2422462 : CollatzResearch.WordTrace tailWord_2422462 prefixEnd_2422462 829258248834670893322871 := by
  unfold tailWord_2422462
  simp only [CollatzResearch.WordTrace]
  refine ⟨11044305968730171552061705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58902965166560914944329093 11044305968730171552061705)
  ·
    refine ⟨8283229476547628664046279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11044305968730171552061705 8283229476547628664046279)
    ·
      refine ⟨12424844214821442996069419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8283229476547628664046279 12424844214821442996069419)
      ·
        refine ⟨18637266322232164494104129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12424844214821442996069419 18637266322232164494104129)
        ·
          refine ⟨13977949741674123370578097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18637266322232164494104129 13977949741674123370578097)
          ·
            refine ⟨10483462306255592527933573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13977949741674123370578097 10483462306255592527933573)
            ·
              refine ⟨1965649182422923598987545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10483462306255592527933573 1965649182422923598987545)
              ·
                refine ⟨1474236886817192699240659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1965649182422923598987545 1474236886817192699240659)
                ·
                  refine ⟨2211355330225789048860989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1474236886817192699240659 2211355330225789048860989)
                  ·
                    refine ⟨829258248834670893322871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2211355330225789048860989 829258248834670893322871)
                    ·
                      rfl

theorem cell22_2422462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_2422462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2422462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2422462 prefixEnd_2422462 := by exact prefixLift 2422462
  have htrace : WordTrace (prefixWord ++ tailWord_2422462) baseStart_2422462 baseEnd_2422462 := by
    simpa [prefixWord, tailWord_2422462, baseEnd_2422462] using wordTrace_append hprefix tailTrace_2422462
  have hstable : (prefixWord ++ tailWord_2422462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422462).length < 2 ^ (prefixWord ++ tailWord_2422462).sum := by decide
  have hdescent : baseEnd_2422462 < baseStart_2422462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422501 : List Nat := [1, 3, 1, 4, 1, 1, 1, 4, 1, 5]
def baseStart_2422501 : Nat := 118140960795 + 2422501 * 2 ^ 59
def prefixEnd_2422501 : Nat := 4983230072969 + 3 ^ 40 * 2422501 * 2
def baseEnd_2422501 : Nat := 829271599331687791597751

theorem tailTrace_2422501 : CollatzResearch.WordTrace tailWord_2422501 prefixEnd_2422501 829271599331687791597751 := by
  unfold tailWord_2422501
  simp only [CollatzResearch.WordTrace]
  refine ⟨88355870196700082077163357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58903913464466721384775571 88355870196700082077163357)
  ·
    refine ⟨33133451323762530778936259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88355870196700082077163357 33133451323762530778936259)
    ·
      refine ⟨49700176985643796168404389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33133451323762530778936259 49700176985643796168404389)
      ·
        refine ⟨9318783184808211781575823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49700176985643796168404389 9318783184808211781575823)
        ·
          refine ⟨13978174777212317672363735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9318783184808211781575823 13978174777212317672363735)
          ·
            refine ⟨20967262165818476508545603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13978174777212317672363735 20967262165818476508545603)
            ·
              refine ⟨31450893248727714762818405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20967262165818476508545603 31450893248727714762818405)
              ·
                refine ⟨5897042484136446518028451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31450893248727714762818405 5897042484136446518028451)
                ·
                  refine ⟨8845563726204669777042677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5897042484136446518028451 8845563726204669777042677)
                  ·
                    refine ⟨829271599331687791597751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8845563726204669777042677 829271599331687791597751)
                    ·
                      rfl

theorem cell22_2422501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 5].length) (baseStart_2422501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2422501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2422501 prefixEnd_2422501 := by exact prefixLift 2422501
  have htrace : WordTrace (prefixWord ++ tailWord_2422501) baseStart_2422501 baseEnd_2422501 := by
    simpa [prefixWord, tailWord_2422501, baseEnd_2422501] using wordTrace_append hprefix tailTrace_2422501
  have hstable : (prefixWord ++ tailWord_2422501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422501).length < 2 ^ (prefixWord ++ tailWord_2422501).sum := by decide
  have hdescent : baseEnd_2422501 < baseStart_2422501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422535 : List Nat := [1, 1, 4, 4, 2, 2, 1, 1, 1, 5]
def baseStart_2422535 : Nat := 118140960795 + 2422535 * 2 ^ 59
def prefixEnd_2422535 : Nat := 4983230072969 + 3 ^ 40 * 2422535 * 2
def baseEnd_2422535 : Nat := 829283238226523036247647

theorem tailTrace_2422535 : CollatzResearch.WordTrace tailWord_2422535 prefixEnd_2422535 829283238226523036247647 := by
  unfold tailWord_2422535
  simp only [CollatzResearch.WordTrace]
  refine ⟨88357110278576905883901059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58904740185717937255934039 88357110278576905883901059)
  ·
    refine ⟨132535665417865358825851589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88357110278576905883901059 132535665417865358825851589)
    ·
      refine ⟨24850437265849754779847173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132535665417865358825851589 24850437265849754779847173)
      ·
        refine ⟨4659456987346829021221345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24850437265849754779847173 4659456987346829021221345)
        ·
          refine ⟨3494592740510121765916009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4659456987346829021221345 3494592740510121765916009)
          ·
            refine ⟨2620944555382591324437007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3494592740510121765916009 2620944555382591324437007)
            ·
              refine ⟨3931416833073886986655511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2620944555382591324437007 3931416833073886986655511)
              ·
                refine ⟨5897125249610830479983267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3931416833073886986655511 5897125249610830479983267)
                ·
                  refine ⟨8845687874416245719974901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5897125249610830479983267 8845687874416245719974901)
                  ·
                    refine ⟨829283238226523036247647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8845687874416245719974901 829283238226523036247647)
                    ·
                      rfl

theorem cell22_2422535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 5].length) (baseStart_2422535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2422535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2422535 prefixEnd_2422535 := by exact prefixLift 2422535
  have htrace : WordTrace (prefixWord ++ tailWord_2422535) baseStart_2422535 baseEnd_2422535 := by
    simpa [prefixWord, tailWord_2422535, baseEnd_2422535] using wordTrace_append hprefix tailTrace_2422535
  have hstable : (prefixWord ++ tailWord_2422535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422535).length < 2 ^ (prefixWord ++ tailWord_2422535).sum := by decide
  have hdescent : baseEnd_2422535 < baseStart_2422535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422651 : List Nat := [1, 1, 1, 1, 1, 5, 1, 4, 1, 6]
def baseStart_2422651 : Nat := 118140960795 + 2422651 * 2 ^ 59
def prefixEnd_2422651 : Nat := 4983230072969 + 3 ^ 40 * 2422651 * 2
def baseEnd_2422651 : Nat := 829322947397137400347291

theorem tailTrace_2422651 : CollatzResearch.WordTrace tailWord_2422651 prefixEnd_2422651 829322947397137400347291 := by
  unfold tailWord_2422651
  simp only [CollatzResearch.WordTrace]
  refine ⟨88361341146156657695123807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58907560764104438463415871 88361341146156657695123807)
  ·
    refine ⟨132542011719234986542685711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88361341146156657695123807 132542011719234986542685711)
    ·
      refine ⟨198813017578852479814028567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132542011719234986542685711 198813017578852479814028567)
      ·
        refine ⟨298219526368278719721042851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198813017578852479814028567 298219526368278719721042851)
        ·
          refine ⟨447329289552418079581564277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298219526368278719721042851 447329289552418079581564277)
          ·
            refine ⟨41937120895539194960771651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 447329289552418079581564277 41937120895539194960771651)
            ·
              refine ⟨62905681343308792441157477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41937120895539194960771651 62905681343308792441157477)
              ·
                refine ⟨11794815251870398582717027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62905681343308792441157477 11794815251870398582717027)
                ·
                  refine ⟨17692222877805597874075541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11794815251870398582717027 17692222877805597874075541)
                  ·
                    refine ⟨829322947397137400347291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17692222877805597874075541 829322947397137400347291)
                    ·
                      rfl

theorem cell22_2422651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 6].length) (baseStart_2422651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2422651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2422651 prefixEnd_2422651 := by exact prefixLift 2422651
  have htrace : WordTrace (prefixWord ++ tailWord_2422651) baseStart_2422651 baseEnd_2422651 := by
    simpa [prefixWord, tailWord_2422651, baseEnd_2422651] using wordTrace_append hprefix tailTrace_2422651
  have hstable : (prefixWord ++ tailWord_2422651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422651).length < 2 ^ (prefixWord ++ tailWord_2422651).sum := by decide
  have hdescent : baseEnd_2422651 < baseStart_2422651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422653 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 6, 3]
def baseStart_2422653 : Nat := 118140960795 + 2422653 * 2 ^ 59
def prefixEnd_2422653 : Nat := 4983230072969 + 3 ^ 40 * 2422653 * 2
def baseEnd_2422653 : Nat := 829323632038010061797285

theorem tailTrace_2422653 : CollatzResearch.WordTrace tailWord_2422653 prefixEnd_2422653 829323632038010061797285 := by
  unfold tailWord_2422653
  simp only [CollatzResearch.WordTrace]
  refine ⟨88361414092149412036696613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58907609394766274691131075 88361414092149412036696613)
  ·
    refine ⟨16567765142278014756880615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88361414092149412036696613 16567765142278014756880615)
    ·
      refine ⟨24851647713417022135320923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16567765142278014756880615 24851647713417022135320923)
      ·
        refine ⟨37277471570125533202981385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24851647713417022135320923 37277471570125533202981385)
        ·
          refine ⟨27958103677594149902236039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37277471570125533202981385 27958103677594149902236039)
          ·
            refine ⟨41937155516391224853354059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27958103677594149902236039 41937155516391224853354059)
            ·
              refine ⟨62905733274586837280031089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41937155516391224853354059 62905733274586837280031089)
              ·
                refine ⟨47179299955940127960023317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62905733274586837280031089 47179299955940127960023317)
                ·
                  refine ⟨2211529685434693498126093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 47179299955940127960023317 2211529685434693498126093)
                  ·
                    refine ⟨829323632038010061797285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2211529685434693498126093 829323632038010061797285)
                    ·
                      rfl

theorem cell22_2422653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 6, 3].length) (baseStart_2422653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2422653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2422653 prefixEnd_2422653 := by exact prefixLift 2422653
  have htrace : WordTrace (prefixWord ++ tailWord_2422653) baseStart_2422653 baseEnd_2422653 := by
    simpa [prefixWord, tailWord_2422653, baseEnd_2422653] using wordTrace_append hprefix tailTrace_2422653
  have hstable : (prefixWord ++ tailWord_2422653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422653).length < 2 ^ (prefixWord ++ tailWord_2422653).sum := by decide
  have hdescent : baseEnd_2422653 < baseStart_2422653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422674 : List Nat := [3, 2, 3, 2, 1, 3, 2, 1, 1, 4]
def baseStart_2422674 : Nat := 118140960795 + 2422674 * 2 ^ 59
def prefixEnd_2422674 : Nat := 4983230072969 + 3 ^ 40 * 2422674 * 2
def baseEnd_2422674 : Nat := 829330820767173007022221

theorem tailTrace_2422674 : CollatzResearch.WordTrace tailWord_2422674 prefixEnd_2422674 829330820767173007022221 := by
  unfold tailWord_2422674
  simp only [CollatzResearch.WordTrace]
  refine ⟨22090545006268333155802769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58908120016715555082140717 22090545006268333155802769)
  ·
    refine ⟨16567908754701249866852077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22090545006268333155802769 16567908754701249866852077)
    ·
      refine ⟨6212965783012968700069529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16567908754701249866852077 6212965783012968700069529)
      ·
        refine ⟨4659724337259726525052147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6212965783012968700069529 4659724337259726525052147)
        ·
          refine ⟨6989586505889589787578221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4659724337259726525052147 6989586505889589787578221)
          ·
            refine ⟨2621094939708596170341833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6989586505889589787578221 2621094939708596170341833)
            ·
              refine ⟨1965821204781447127756375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2621094939708596170341833 1965821204781447127756375)
              ·
                refine ⟨2948731807172170691634563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1965821204781447127756375 2948731807172170691634563)
                ·
                  refine ⟨4423097710758256037451845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2948731807172170691634563 4423097710758256037451845)
                  ·
                    refine ⟨829330820767173007022221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4423097710758256037451845 829330820767173007022221)
                    ·
                      rfl

theorem cell22_2422674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_2422674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2422674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2422674 prefixEnd_2422674 := by exact prefixLift 2422674
  have htrace : WordTrace (prefixWord ++ tailWord_2422674) baseStart_2422674 baseEnd_2422674 := by
    simpa [prefixWord, tailWord_2422674, baseEnd_2422674] using wordTrace_append hprefix tailTrace_2422674
  have hstable : (prefixWord ++ tailWord_2422674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422674).length < 2 ^ (prefixWord ++ tailWord_2422674).sum := by decide
  have hdescent : baseEnd_2422674 < baseStart_2422674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422728 : List Nat := [2, 1, 3, 1, 4, 1, 1, 2, 7]
def baseStart_2422728 : Nat := 118140960795 + 2422728 * 2 ^ 59
def prefixEnd_2422728 : Nat := 4983230072969 + 3 ^ 40 * 2422728 * 2
def baseEnd_2422728 : Nat := 276449768690244955390685

theorem tailTrace_2422728 : CollatzResearch.WordTrace tailWord_2422728 prefixEnd_2422728 276449768690244955390685 := by
  unfold tailWord_2422728
  simp only [CollatzResearch.WordTrace]
  refine ⟨44182074783438849922838419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58909433044585133230451225 44182074783438849922838419)
  ·
    refine ⟨66273112175158274884257629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44182074783438849922838419 66273112175158274884257629)
    ·
      refine ⟨24852417065684353081596611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66273112175158274884257629 24852417065684353081596611)
      ·
        refine ⟨37278625598526529622394917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24852417065684353081596611 37278625598526529622394917)
        ·
          refine ⟨6989742299723724304199047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37278625598526529622394917 6989742299723724304199047)
          ·
            refine ⟨10484613449585586456298571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6989742299723724304199047 10484613449585586456298571)
            ·
              refine ⟨15726920174378379684447857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10484613449585586456298571 15726920174378379684447857)
              ·
                refine ⟨11795190130783784763335893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15726920174378379684447857 11795190130783784763335893)
                ·
                  refine ⟨276449768690244955390685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11795190130783784763335893 276449768690244955390685)
                  ·
                    rfl

theorem cell22_2422728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 7].length) (baseStart_2422728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2422728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2422728 prefixEnd_2422728 := by exact prefixLift 2422728
  have htrace : WordTrace (prefixWord ++ tailWord_2422728) baseStart_2422728 baseEnd_2422728 := by
    simpa [prefixWord, tailWord_2422728, baseEnd_2422728] using wordTrace_append hprefix tailTrace_2422728
  have hstable : (prefixWord ++ tailWord_2422728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422728).length < 2 ^ (prefixWord ++ tailWord_2422728).sum := by decide
  have hdescent : baseEnd_2422728 < baseStart_2422728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422749 : List Nat := [1, 4, 3, 1, 3, 2, 1, 1, 3, 3]
def baseStart_2422749 : Nat := 118140960795 + 2422749 * 2 ^ 59
def prefixEnd_2422749 : Nat := 4983230072969 + 3 ^ 40 * 2422749 * 2
def baseEnd_2422749 : Nat := 829356494799897811396991

theorem tailTrace_2422749 : CollatzResearch.WordTrace tailWord_2422749 prefixEnd_2422749 829356494799897811396991 := by
  unfold tailWord_2422749
  simp only [CollatzResearch.WordTrace]
  refine ⟨88364915499801620432191301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58909943666534413621460867 88364915499801620432191301)
  ·
    refine ⟨16568421656212803831035869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88364915499801620432191301 16568421656212803831035869)
    ·
      refine ⟨6213158121079801436638451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16568421656212803831035869 6213158121079801436638451)
      ·
        refine ⟨9319737181619702154957677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6213158121079801436638451 9319737181619702154957677)
        ·
          refine ⟨3494901443107388308109129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9319737181619702154957677 3494901443107388308109129)
          ·
            refine ⟨2621176082330541231081847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3494901443107388308109129 2621176082330541231081847)
            ·
              refine ⟨3931764123495811846622771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2621176082330541231081847 3931764123495811846622771)
              ·
                refine ⟨5897646185243717769934157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3931764123495811846622771 5897646185243717769934157)
                ·
                  refine ⟨2211617319466394163725309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5897646185243717769934157 2211617319466394163725309)
                  ·
                    refine ⟨829356494799897811396991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2211617319466394163725309 829356494799897811396991)
                    ·
                      rfl

theorem cell22_2422749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_2422749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2422749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2422749 prefixEnd_2422749 := by exact prefixLift 2422749
  have htrace : WordTrace (prefixWord ++ tailWord_2422749) baseStart_2422749 baseEnd_2422749 := by
    simpa [prefixWord, tailWord_2422749, baseEnd_2422749] using wordTrace_append hprefix tailTrace_2422749
  have hstable : (prefixWord ++ tailWord_2422749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422749).length < 2 ^ (prefixWord ++ tailWord_2422749).sum := by decide
  have hdescent : baseEnd_2422749 < baseStart_2422749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422792 : List Nat := [2, 1, 3, 2, 1, 2, 5, 1, 1, 4]
def baseStart_2422792 : Nat := 118140960795 + 2422792 * 2 ^ 59
def prefixEnd_2422792 : Nat := 4983230072969 + 3 ^ 40 * 2422792 * 2
def baseEnd_2422792 : Nat := 829371214578660032571859

theorem tailTrace_2422792 : CollatzResearch.WordTrace tailWord_2422792 prefixEnd_2422792 829371214578660032571859 := by
  unfold tailWord_2422792
  simp only [CollatzResearch.WordTrace]
  refine ⟨44183241919322919388003315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58910989225763892517337753 44183241919322919388003315)
  ·
    refine ⟨66274862878984379082004973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44183241919322919388003315 66274862878984379082004973)
    ·
      refine ⟨24853073579619142155751865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66274862878984379082004973 24853073579619142155751865)
      ·
        refine ⟨18639805184714356616813899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24853073579619142155751865 18639805184714356616813899)
        ·
          refine ⟨27959707777071534925220849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18639805184714356616813899 27959707777071534925220849)
          ·
            refine ⟨20969780832803651193915637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27959707777071534925220849 20969780832803651193915637)
            ·
              refine ⟨1965916953075342299429591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20969780832803651193915637 1965916953075342299429591)
              ·
                refine ⟨2948875429613013449144387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1965916953075342299429591 2948875429613013449144387)
                ·
                  refine ⟨4423313144419520173716581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2948875429613013449144387 4423313144419520173716581)
                  ·
                    refine ⟨829371214578660032571859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4423313144419520173716581 829371214578660032571859)
                    ·
                      rfl

theorem cell22_2422792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 1, 1, 4].length) (baseStart_2422792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2422792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2422792 prefixEnd_2422792 := by exact prefixLift 2422792
  have htrace : WordTrace (prefixWord ++ tailWord_2422792) baseStart_2422792 baseEnd_2422792 := by
    simpa [prefixWord, tailWord_2422792, baseEnd_2422792] using wordTrace_append hprefix tailTrace_2422792
  have hstable : (prefixWord ++ tailWord_2422792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422792).length < 2 ^ (prefixWord ++ tailWord_2422792).sum := by decide
  have hdescent : baseEnd_2422792 < baseStart_2422792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422863 : List Nat := [1, 1, 2, 1, 1, 2, 2, 5, 7]
def baseStart_2422863 : Nat := 118140960795 + 2422863 * 2 ^ 59
def prefixEnd_2422863 : Nat := 4983230072969 + 3 ^ 40 * 2422863 * 2
def baseEnd_2422863 : Nat := 276465173109879838015547

theorem tailTrace_2422863 : CollatzResearch.WordTrace tailWord_2422863 prefixEnd_2422863 276465173109879838015547 := by
  unfold tailWord_2422863
  simp only [CollatzResearch.WordTrace]
  refine ⟨88369073421388617901841243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58912715614259078601227495 88369073421388617901841243)
  ·
    refine ⟨132553610132082926852761865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88369073421388617901841243 132553610132082926852761865)
    ·
      refine ⟨99415207599062195139571399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132553610132082926852761865 99415207599062195139571399)
      ·
        refine ⟨149122811398593292709357099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99415207599062195139571399 149122811398593292709357099)
        ·
          refine ⟨223684217097889939064035649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149122811398593292709357099 223684217097889939064035649)
          ·
            refine ⟨167763162823417454298026737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 223684217097889939064035649 167763162823417454298026737)
            ·
              refine ⟨125822372117563090723520053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167763162823417454298026737 125822372117563090723520053)
              ·
                refine ⟨11795847386021539755330005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 125822372117563090723520053 11795847386021539755330005)
                ·
                  refine ⟨276465173109879838015547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11795847386021539755330005 276465173109879838015547)
                  ·
                    rfl

theorem cell22_2422863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 7].length) (baseStart_2422863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2422863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2422863 prefixEnd_2422863 := by exact prefixLift 2422863
  have htrace : WordTrace (prefixWord ++ tailWord_2422863) baseStart_2422863 baseEnd_2422863 := by
    simpa [prefixWord, tailWord_2422863, baseEnd_2422863] using wordTrace_append hprefix tailTrace_2422863
  have hstable : (prefixWord ++ tailWord_2422863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422863).length < 2 ^ (prefixWord ++ tailWord_2422863).sum := by decide
  have hdescent : baseEnd_2422863 < baseStart_2422863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422944 : List Nat := [2, 1, 1, 4, 2, 4, 1, 2, 1, 4]
def baseStart_2422944 : Nat := 118140960795 + 2422944 * 2 ^ 59
def prefixEnd_2422944 : Nat := 4983230072969 + 3 ^ 40 * 2422944 * 2
def baseEnd_2422944 : Nat := 829423247284982302771393

theorem tailTrace_2422944 : CollatzResearch.WordTrace tailWord_2422944 prefixEnd_2422944 829423247284982302771393 := by
  unfold tailWord_2422944
  simp only [CollatzResearch.WordTrace]
  refine ⟨44186013867047584367769943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58914685156063445823693257 44186013867047584367769943)
  ·
    refine ⟨66279020800571376551654915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44186013867047584367769943 66279020800571376551654915)
    ·
      refine ⟨99418531200857064827482373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66279020800571376551654915 99418531200857064827482373)
      ·
        refine ⟨18640974600160699655152945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99418531200857064827482373 18640974600160699655152945)
        ·
          refine ⟨13980730950120524741364709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18640974600160699655152945 13980730950120524741364709)
          ·
            refine ⟨2621387053147598389005883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13980730950120524741364709 2621387053147598389005883)
            ·
              refine ⟨3932080579721397583508825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2621387053147598389005883 3932080579721397583508825)
              ·
                refine ⟨2949060434791048187631619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3932080579721397583508825 2949060434791048187631619)
                ·
                  refine ⟨4423590652186572281447429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2949060434791048187631619 4423590652186572281447429)
                  ·
                    refine ⟨829423247284982302771393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4423590652186572281447429 829423247284982302771393)
                    ·
                      rfl

theorem cell22_2422944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 2, 1, 4].length) (baseStart_2422944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2422944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2422944 prefixEnd_2422944 := by exact prefixLift 2422944
  have htrace : WordTrace (prefixWord ++ tailWord_2422944) baseStart_2422944 baseEnd_2422944 := by
    simpa [prefixWord, tailWord_2422944, baseEnd_2422944] using wordTrace_append hprefix tailTrace_2422944
  have hstable : (prefixWord ++ tailWord_2422944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422944).length < 2 ^ (prefixWord ++ tailWord_2422944).sum := by decide
  have hdescent : baseEnd_2422944 < baseStart_2422944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422957 : List Nat := [1, 5, 2, 1, 2, 1, 1, 1, 3, 5]
def baseStart_2422957 : Nat := 118140960795 + 2422957 * 2 ^ 59
def prefixEnd_2422957 : Nat := 4983230072969 + 3 ^ 40 * 2422957 * 2
def baseEnd_2422957 : Nat := 829427697450654602196353

theorem tailTrace_2422957 : CollatzResearch.WordTrace tailWord_2422957 prefixEnd_2422957 829427697450654602196353 := by
  unfold tailWord_2422957
  simp only [CollatzResearch.WordTrace]
  refine ⟨88372501883048071955763125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58915001255365381303842083 88372501883048071955763125)
  ·
    refine ⟨8284922051535756745852793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88372501883048071955763125 8284922051535756745852793)
    ·
      refine ⟨6213691538651817559389595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8284922051535756745852793 6213691538651817559389595)
      ·
        refine ⟨9320537307977726339084393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6213691538651817559389595 9320537307977726339084393)
        ·
          refine ⟨6990402980983294754313295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9320537307977726339084393 6990402980983294754313295)
          ·
            refine ⟨10485604471474942131469943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6990402980983294754313295 10485604471474942131469943)
            ·
              refine ⟨15728406707212413197204915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10485604471474942131469943 15728406707212413197204915)
              ·
                refine ⟨23592610060818619795807373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15728406707212413197204915 23592610060818619795807373)
                ·
                  refine ⟨8847228772806982423427765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23592610060818619795807373 8847228772806982423427765)
                  ·
                    refine ⟨829427697450654602196353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8847228772806982423427765 829427697450654602196353)
                    ·
                      rfl

theorem cell22_2422957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_2422957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2422957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2422957 prefixEnd_2422957 := by exact prefixLift 2422957
  have htrace : WordTrace (prefixWord ++ tailWord_2422957) baseStart_2422957 baseEnd_2422957 := by
    simpa [prefixWord, tailWord_2422957, baseEnd_2422957] using wordTrace_append hprefix tailTrace_2422957
  have hstable : (prefixWord ++ tailWord_2422957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422957).length < 2 ^ (prefixWord ++ tailWord_2422957).sum := by decide
  have hdescent : baseEnd_2422957 < baseStart_2422957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422961 : List Nat := [1, 2, 2, 5, 2, 1, 3, 1, 1, 4]
def baseStart_2422961 : Nat := 118140960795 + 2422961 * 2 ^ 59
def prefixEnd_2422961 : Nat := 4983230072969 + 3 ^ 40 * 2422961 * 2
def baseEnd_2422961 : Nat := 829429066732399925096341

theorem tailTrace_2422961 : CollatzResearch.WordTrace tailWord_2422961 prefixEnd_2422961 829429066732399925096341 := by
  unfold tailWord_2422961
  simp only [CollatzResearch.WordTrace]
  refine ⟨88372647775033580638908737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58915098516689053759272491 88372647775033580638908737)
  ·
    refine ⟨66279485831275185479181553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88372647775033580638908737 66279485831275185479181553)
    ·
      refine ⟨49709614373456389109386165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66279485831275185479181553 49709614373456389109386165)
      ·
        refine ⟨4660276347511536479004953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49709614373456389109386165 4660276347511536479004953)
        ·
          refine ⟨3495207260633652359253715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4660276347511536479004953 3495207260633652359253715)
          ·
            refine ⟨5242810890950478538880573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3495207260633652359253715 5242810890950478538880573)
            ·
              refine ⟨1966054084106429452080215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5242810890950478538880573 1966054084106429452080215)
              ·
                refine ⟨2949081126159644178120323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1966054084106429452080215 2949081126159644178120323)
                ·
                  refine ⟨4423621689239466267180485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2949081126159644178120323 4423621689239466267180485)
                  ·
                    refine ⟨829429066732399925096341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4423621689239466267180485 829429066732399925096341)
                    ·
                      rfl

theorem cell22_2422961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 1, 1, 4].length) (baseStart_2422961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2422961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2422961 prefixEnd_2422961 := by exact prefixLift 2422961
  have htrace : WordTrace (prefixWord ++ tailWord_2422961) baseStart_2422961 baseEnd_2422961 := by
    simpa [prefixWord, tailWord_2422961, baseEnd_2422961] using wordTrace_append hprefix tailTrace_2422961
  have hstable : (prefixWord ++ tailWord_2422961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422961).length < 2 ^ (prefixWord ++ tailWord_2422961).sum := by decide
  have hdescent : baseEnd_2422961 < baseStart_2422961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422976 : List Nat := [2, 1, 1, 2, 5, 3, 2, 2, 4]
def baseStart_2422976 : Nat := 118140960795 + 2422976 * 2 ^ 59
def prefixEnd_2422976 : Nat := 4983230072969 + 3 ^ 40 * 2422976 * 2
def baseEnd_2422976 : Nat := 276478067179648295323765

theorem tailTrace_2422976 : CollatzResearch.WordTrace tailWord_2422976 prefixEnd_2422976 276478067179648295323765 := by
  unfold tailWord_2422976
  simp only [CollatzResearch.WordTrace]
  refine ⟨44186597434989619100352391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58915463246652825467136521 44186597434989619100352391)
  ·
    refine ⟨66279896152484428650528587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44186597434989619100352391 66279896152484428650528587)
    ·
      refine ⟨99419844228726642975792881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66279896152484428650528587 99419844228726642975792881)
      ·
        refine ⟨74564883171544982231844661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99419844228726642975792881 74564883171544982231844661)
        ·
          refine ⟨6990457797332342084235437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74564883171544982231844661 6990457797332342084235437)
          ·
            refine ⟨2621421673999628281588289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6990457797332342084235437 2621421673999628281588289)
            ·
              refine ⟨1966066255499721211191217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2621421673999628281588289 1966066255499721211191217)
              ·
                refine ⟨1474549691624790908393413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1966066255499721211191217 1474549691624790908393413)
                ·
                  refine ⟨276478067179648295323765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1474549691624790908393413 276478067179648295323765)
                  ·
                    rfl

theorem cell22_2422976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 2, 4].length) (baseStart_2422976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2422976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2422976 prefixEnd_2422976 := by exact prefixLift 2422976
  have htrace : WordTrace (prefixWord ++ tailWord_2422976) baseStart_2422976 baseEnd_2422976 := by
    simpa [prefixWord, tailWord_2422976, baseEnd_2422976] using wordTrace_append hprefix tailTrace_2422976
  have hstable : (prefixWord ++ tailWord_2422976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422976).length < 2 ^ (prefixWord ++ tailWord_2422976).sum := by decide
  have hdescent : baseEnd_2422976 < baseStart_2422976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423002 : List Nat := [3, 1, 1, 2, 2, 1, 3, 1, 5, 3]
def baseStart_2423002 : Nat := 118140960795 + 2423002 * 2 ^ 59
def prefixEnd_2423002 : Nat := 4983230072969 + 3 ^ 40 * 2423002 * 2
def baseEnd_2423002 : Nat := 829443101870289484821215

theorem tailTrace_2423002 : CollatzResearch.WordTrace tailWord_2423002 prefixEnd_2423002 829443101870289484821215 := by
  unfold tailWord_2423002
  simp only [CollatzResearch.WordTrace]
  refine ⟨22093535791971261160287815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58916095445256696427434173 22093535791971261160287815)
  ·
    refine ⟨33140303687956891740431723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22093535791971261160287815 33140303687956891740431723)
    ·
      refine ⟨49710455531935337610647585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33140303687956891740431723 49710455531935337610647585)
      ·
        refine ⟨37282841648951503207985689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49710455531935337610647585 37282841648951503207985689)
        ·
          refine ⟨27962131236713627405989267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37282841648951503207985689 27962131236713627405989267)
          ·
            refine ⟨41943196855070441108983901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27962131236713627405989267 41943196855070441108983901)
            ·
              refine ⟨15728698820651415415868963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41943196855070441108983901 15728698820651415415868963)
              ·
                refine ⟨23593048230977123123803445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15728698820651415415868963 23593048230977123123803445)
                ·
                  refine ⟨2211848271654105292856573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23593048230977123123803445 2211848271654105292856573)
                  ·
                    refine ⟨829443101870289484821215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2211848271654105292856573 829443101870289484821215)
                    ·
                      rfl

theorem cell22_2423002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 5, 3].length) (baseStart_2423002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2423002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2423002 prefixEnd_2423002 := by exact prefixLift 2423002
  have htrace : WordTrace (prefixWord ++ tailWord_2423002) baseStart_2423002 baseEnd_2423002 := by
    simpa [prefixWord, tailWord_2423002, baseEnd_2423002] using wordTrace_append hprefix tailTrace_2423002
  have hstable : (prefixWord ++ tailWord_2423002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423002).length < 2 ^ (prefixWord ++ tailWord_2423002).sum := by decide
  have hdescent : baseEnd_2423002 < baseStart_2423002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423010 : List Nat := [3, 3, 4, 1, 1, 1, 2, 3, 4]
def baseStart_2423010 : Nat := 118140960795 + 2423010 * 2 ^ 59
def prefixEnd_2423010 : Nat := 4983230072969 + 3 ^ 40 * 2423010 * 2
def baseEnd_2423010 : Nat := 276481946811260043540397

theorem tailTrace_2423010 : CollatzResearch.WordTrace tailWord_2423010 prefixEnd_2423010 276481946811260043540397 := by
  unfold tailWord_2423010
  simp only [CollatzResearch.WordTrace]
  refine ⟨22093608737964015501860621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58916289967904041338294989 22093608737964015501860621)
  ·
    refine ⟨8285103276736505813197733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22093608737964015501860621 8285103276736505813197733)
    ·
      refine ⟨1553456864388094839974575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8285103276736505813197733 1553456864388094839974575)
      ·
        refine ⟨2330185296582142259961863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1553456864388094839974575 2330185296582142259961863)
        ·
          refine ⟨3495277944873213389942795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2330185296582142259961863 3495277944873213389942795)
          ·
            refine ⟨5242916917309820084914193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3495277944873213389942795 5242916917309820084914193)
            ·
              refine ⟨3932187687982365063685645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5242916917309820084914193 3932187687982365063685645)
              ·
                refine ⟨1474570382993386898882117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3932187687982365063685645 1474570382993386898882117)
                ·
                  refine ⟨276481946811260043540397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1474570382993386898882117 276481946811260043540397)
                  ·
                    rfl

theorem cell22_2423010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_2423010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2423010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2423010 prefixEnd_2423010 := by exact prefixLift 2423010
  have htrace : WordTrace (prefixWord ++ tailWord_2423010) baseStart_2423010 baseEnd_2423010 := by
    simpa [prefixWord, tailWord_2423010, baseEnd_2423010] using wordTrace_append hprefix tailTrace_2423010
  have hstable : (prefixWord ++ tailWord_2423010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423010).length < 2 ^ (prefixWord ++ tailWord_2423010).sum := by decide
  have hdescent : baseEnd_2423010 < baseStart_2423010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423036 : List Nat := [2, 2, 2, 1, 4, 1, 2, 4, 1, 3]
def baseStart_2423036 : Nat := 118140960795 + 2423036 * 2 ^ 59
def prefixEnd_2423036 : Nat := 4983230072969 + 3 ^ 40 * 2423036 * 2
def baseEnd_2423036 : Nat := 829454740765124729471111

theorem tailTrace_2423036 : CollatzResearch.WordTrace tailWord_2423036 prefixEnd_2423036 829454740765124729471111 := by
  unfold tailWord_2423036
  simp only [CollatzResearch.WordTrace]
  refine ⟨44187691624880934223944481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58916922166507912298592641 44187691624880934223944481)
  ·
    refine ⟨33140768718660700667958361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44187691624880934223944481 33140768718660700667958361)
    ·
      refine ⟨24855576538995525500968771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33140768718660700667958361 24855576538995525500968771)
      ·
        refine ⟨37283364808493288251453157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24855576538995525500968771 37283364808493288251453157)
        ·
          refine ⟨6990630901592491547147467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37283364808493288251453157 6990630901592491547147467)
          ·
            refine ⟨10485946352388737320721201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6990630901592491547147467 10485946352388737320721201)
            ·
              refine ⟨7864459764291552990540901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10485946352388737320721201 7864459764291552990540901)
              ·
                refine ⟨1474586205804666185726419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7864459764291552990540901 1474586205804666185726419)
                ·
                  refine ⟨2211879308706999278589629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1474586205804666185726419 2211879308706999278589629)
                  ·
                    refine ⟨829454740765124729471111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2211879308706999278589629 829454740765124729471111)
                    ·
                      rfl

theorem cell22_2423036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 4, 1, 3].length) (baseStart_2423036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2423036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2423036 prefixEnd_2423036 := by exact prefixLift 2423036
  have htrace : WordTrace (prefixWord ++ tailWord_2423036) baseStart_2423036 baseEnd_2423036 := by
    simpa [prefixWord, tailWord_2423036, baseEnd_2423036] using wordTrace_append hprefix tailTrace_2423036
  have hstable : (prefixWord ++ tailWord_2423036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423036).length < 2 ^ (prefixWord ++ tailWord_2423036).sum := by decide
  have hdescent : baseEnd_2423036 < baseStart_2423036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423045 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 2, 8]
def baseStart_2423045 : Nat := 118140960795 + 2423045 * 2 ^ 59
def prefixEnd_2423045 : Nat := 4983230072969 + 3 ^ 40 * 2423045 * 2
def baseEnd_2423045 : Nat := 829457821649051705996083

theorem tailTrace_2423045 : CollatzResearch.WordTrace tailWord_2423045 prefixEnd_2423045 829457821649051705996083 := by
  unfold tailWord_2423045
  simp only [CollatzResearch.WordTrace]
  refine ⟨88375711506729262984966589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58917141004486175323311059 88375711506729262984966589)
  ·
    refine ⟨33140891815023473619362471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88375711506729262984966589 33140891815023473619362471)
    ·
      refine ⟨49711337722535210429043707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33140891815023473619362471 49711337722535210429043707)
      ·
        refine ⟨74567006583802815643565561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49711337722535210429043707 74567006583802815643565561)
        ·
          refine ⟨55925254937852111732674171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74567006583802815643565561 55925254937852111732674171)
          ·
            refine ⟨83887882406778167599011257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55925254937852111732674171 83887882406778167599011257)
            ·
              refine ⟨62915911805083625699258443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83887882406778167599011257 62915911805083625699258443)
              ·
                refine ⟨94373867707625438548887665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62915911805083625699258443 94373867707625438548887665)
                ·
                  refine ⟨70780400780719078911665749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94373867707625438548887665 70780400780719078911665749)
                  ·
                    refine ⟨829457821649051705996083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 70780400780719078911665749 829457821649051705996083)
                    ·
                      rfl

theorem cell22_2423045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_2423045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2423045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2423045 prefixEnd_2423045 := by exact prefixLift 2423045
  have htrace : WordTrace (prefixWord ++ tailWord_2423045) baseStart_2423045 baseEnd_2423045 := by
    simpa [prefixWord, tailWord_2423045, baseEnd_2423045] using wordTrace_append hprefix tailTrace_2423045
  have hstable : (prefixWord ++ tailWord_2423045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423045).length < 2 ^ (prefixWord ++ tailWord_2423045).sum := by decide
  have hdescent : baseEnd_2423045 < baseStart_2423045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423049 : List Nat := [1, 2, 1, 1, 3, 5, 3, 1, 5]
def baseStart_2423049 : Nat := 118140960795 + 2423049 * 2 ^ 59
def prefixEnd_2423049 : Nat := 4983230072969 + 3 ^ 40 * 2423049 * 2
def baseEnd_2423049 : Nat := 276486396976932342965357

theorem tailTrace_2423049 : CollatzResearch.WordTrace tailWord_2423049 prefixEnd_2423049 276486396976932342965357 := by
  unfold tailWord_2423049
  simp only [CollatzResearch.WordTrace]
  refine ⟨88375857398714771668112201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58917238265809847778741467 88375857398714771668112201)
  ·
    refine ⟨66281893049036078751084151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88375857398714771668112201 66281893049036078751084151)
    ·
      refine ⟨99422839573554118126626227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66281893049036078751084151 99422839573554118126626227)
      ·
        refine ⟨149134259360331177189939341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99422839573554118126626227 149134259360331177189939341)
        ·
          refine ⟨55925347260124191446227253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149134259360331177189939341 55925347260124191446227253)
          ·
            refine ⟨5243001305636642948083805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55925347260124191446227253 5243001305636642948083805)
            ·
              refine ⟨1966125489613741105531427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5243001305636642948083805 1966125489613741105531427)
              ·
                refine ⟨2949188234420611658297141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1966125489613741105531427 2949188234420611658297141)
                ·
                  refine ⟨276486396976932342965357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2949188234420611658297141 276486396976932342965357)
                  ·
                    rfl

theorem cell22_2423049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 1, 5].length) (baseStart_2423049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2423049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2423049 prefixEnd_2423049 := by exact prefixLift 2423049
  have htrace : WordTrace (prefixWord ++ tailWord_2423049) baseStart_2423049 baseEnd_2423049 := by
    simpa [prefixWord, tailWord_2423049, baseEnd_2423049] using wordTrace_append hprefix tailTrace_2423049
  have hstable : (prefixWord ++ tailWord_2423049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423049).length < 2 ^ (prefixWord ++ tailWord_2423049).sum := by decide
  have hdescent : baseEnd_2423049 < baseStart_2423049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423070 : List Nat := [4, 3, 2, 1, 1, 1, 3, 3, 1, 3]
def baseStart_2423070 : Nat := 118140960795 + 2423070 * 2 ^ 59
def prefixEnd_2423070 : Nat := 4983230072969 + 3 ^ 40 * 2423070 * 2
def baseEnd_2423070 : Nat := 829466379659959974121007

theorem tailTrace_2423070 : CollatzResearch.WordTrace tailWord_2423070 prefixEnd_2423070 829466379659959974121007 := by
  unfold tailWord_2423070
  simp only [CollatzResearch.WordTrace]
  refine ⟨11047077916454836531828333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58917748887759128169751109 11047077916454836531828333)
  ·
    refine ⟨4142654218670563699435625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11047077916454836531828333 4142654218670563699435625)
    ·
      refine ⟨3106990664002922774576719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4142654218670563699435625 3106990664002922774576719)
      ·
        refine ⟨4660485996004384161865079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3106990664002922774576719 4660485996004384161865079)
        ·
          refine ⟨6990728994006576242797619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4660485996004384161865079 6990728994006576242797619)
          ·
            refine ⟨10486093491009864364196429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6990728994006576242797619 10486093491009864364196429)
            ·
              refine ⟨3932285059128699136573661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10486093491009864364196429 3932285059128699136573661)
              ·
                refine ⟨1474606897173262176215123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3932285059128699136573661 1474606897173262176215123)
                ·
                  refine ⟨2211910345759893264322685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1474606897173262176215123 2211910345759893264322685)
                  ·
                    refine ⟨829466379659959974121007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2211910345759893264322685 829466379659959974121007)
                    ·
                      rfl

theorem cell22_2423070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_2423070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2423070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2423070 prefixEnd_2423070 := by exact prefixLift 2423070
  have htrace : WordTrace (prefixWord ++ tailWord_2423070) baseStart_2423070 baseEnd_2423070 := by
    simpa [prefixWord, tailWord_2423070, baseEnd_2423070] using wordTrace_append hprefix tailTrace_2423070
  have hstable : (prefixWord ++ tailWord_2423070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423070).length < 2 ^ (prefixWord ++ tailWord_2423070).sum := by decide
  have hdescent : baseEnd_2423070 < baseStart_2423070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423122 : List Nat := [3, 2, 2, 1, 1, 1, 4, 8]
def baseStart_2423122 : Nat := 118140960795 + 2423122 * 2 ^ 59
def prefixEnd_2423122 : Nat := 4983230072969 + 3 ^ 40 * 2423122 * 2
def baseEnd_2423122 : Nat := 92164908924738796868983

theorem tailTrace_2423122 : CollatzResearch.WordTrace tailWord_2423122 prefixEnd_2423122 92164908924738796868983 := by
  unfold tailWord_2423122
  simp only [CollatzResearch.WordTrace]
  refine ⟨22094629981862576283879905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58919013284966870090346413 22094629981862576283879905)
  ·
    refine ⟨16570972486396932212909929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22094629981862576283879905 16570972486396932212909929)
    ·
      refine ⟨12428229364797699159682447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16570972486396932212909929 12428229364797699159682447)
      ·
        refine ⟨18642344047196548739523671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12428229364797699159682447 18642344047196548739523671)
        ·
          refine ⟨27963516070794823109285507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18642344047196548739523671 27963516070794823109285507)
          ·
            refine ⟨41945274106192234663928261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27963516070794823109285507 41945274106192234663928261)
            ·
              refine ⟨7864738894911043999486549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41945274106192234663928261 7864738894911043999486549)
              ·
                refine ⟨92164908924738796868983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7864738894911043999486549 92164908924738796868983)
                ·
                  rfl

theorem cell22_2423122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 8].length) (baseStart_2423122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2423122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2423122 prefixEnd_2423122 := by exact prefixLift 2423122
  have htrace : WordTrace (prefixWord ++ tailWord_2423122) baseStart_2423122 baseEnd_2423122 := by
    simpa [prefixWord, tailWord_2423122, baseEnd_2423122] using wordTrace_append hprefix tailTrace_2423122
  have hstable : (prefixWord ++ tailWord_2423122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423122).length < 2 ^ (prefixWord ++ tailWord_2423122).sum := by decide
  have hdescent : baseEnd_2423122 < baseStart_2423122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423124 : List Nat := [2, 4, 1, 1, 2, 2, 1, 3, 2, 4]
def baseStart_2423124 : Nat := 118140960795 + 2423124 * 2 ^ 59
def prefixEnd_2423124 : Nat := 4983230072969 + 3 ^ 40 * 2423124 * 2
def baseEnd_2423124 : Nat := 829484864963521833270841

theorem tailTrace_2423124 : CollatzResearch.WordTrace tailWord_2423124 prefixEnd_2423124 829484864963521833270841 := by
  unfold tailWord_2423124
  simp only [CollatzResearch.WordTrace]
  refine ⟨44189296436721529738546213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58919061915628706318061617 44189296436721529738546213)
  ·
    refine ⟨8285493081885286825977415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44189296436721529738546213 8285493081885286825977415)
    ·
      refine ⟨12428239622827930238966123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8285493081885286825977415 12428239622827930238966123)
      ·
        refine ⟨18642359434241895358449185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12428239622827930238966123 18642359434241895358449185)
        ·
          refine ⟨13981769575681421518836889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18642359434241895358449185 13981769575681421518836889)
          ·
            refine ⟨10486327181761066139127667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13981769575681421518836889 10486327181761066139127667)
            ·
              refine ⟨15729490772641599208691501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10486327181761066139127667 15729490772641599208691501)
              ·
                refine ⟨5898559039740599703259313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15729490772641599208691501 5898559039740599703259313)
                ·
                  refine ⟨4423919279805449777444485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5898559039740599703259313 4423919279805449777444485)
                  ·
                    refine ⟨829484864963521833270841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4423919279805449777444485 829484864963521833270841)
                    ·
                      rfl

theorem cell22_2423124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_2423124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2423124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2423124 prefixEnd_2423124 := by exact prefixLift 2423124
  have htrace : WordTrace (prefixWord ++ tailWord_2423124) baseStart_2423124 baseEnd_2423124 := by
    simpa [prefixWord, tailWord_2423124, baseEnd_2423124] using wordTrace_append hprefix tailTrace_2423124
  have hstable : (prefixWord ++ tailWord_2423124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423124).length < 2 ^ (prefixWord ++ tailWord_2423124).sum := by decide
  have hdescent : baseEnd_2423124 < baseStart_2423124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423152 : List Nat := [2, 1, 1, 1, 4, 3, 1, 1, 2, 6]
def baseStart_2423152 : Nat := 118140960795 + 2423152 * 2 ^ 59
def prefixEnd_2423152 : Nat := 4983230072969 + 3 ^ 40 * 2423152 * 2
def baseEnd_2423152 : Nat := 829494449935739093570755

theorem tailTrace_2423152 : CollatzResearch.WordTrace tailWord_2423152 prefixEnd_2423152 829494449935739093570755 := by
  unfold tailWord_2423152
  simp only [CollatzResearch.WordTrace]
  refine ⟨44189807058670810129555855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58919742744894413506074473 44189807058670810129555855)
  ·
    refine ⟨66284710588006215194333783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44189807058670810129555855 66284710588006215194333783)
    ·
      refine ⟨99427065882009322791500675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66284710588006215194333783 99427065882009322791500675)
      ·
        refine ⟨149140598823013984187251013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99427065882009322791500675 149140598823013984187251013)
        ·
          refine ⟨27963862279315122035109565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 149140598823013984187251013 27963862279315122035109565)
          ·
            refine ⟨10486448354743170763166087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27963862279315122035109565 10486448354743170763166087)
            ·
              refine ⟨15729672532114756144749131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10486448354743170763166087 15729672532114756144749131)
              ·
                refine ⟨23594508798172134217123697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15729672532114756144749131 23594508798172134217123697)
                ·
                  refine ⟨17695881598629100662842773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23594508798172134217123697 17695881598629100662842773)
                  ·
                    refine ⟨829494449935739093570755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17695881598629100662842773 829494449935739093570755)
                    ·
                      rfl

theorem cell22_2423152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 2, 6].length) (baseStart_2423152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2423152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2423152 prefixEnd_2423152 := by exact prefixLift 2423152
  have htrace : WordTrace (prefixWord ++ tailWord_2423152) baseStart_2423152 baseEnd_2423152 := by
    simpa [prefixWord, tailWord_2423152, baseEnd_2423152] using wordTrace_append hprefix tailTrace_2423152
  have hstable : (prefixWord ++ tailWord_2423152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423152).length < 2 ^ (prefixWord ++ tailWord_2423152).sum := by decide
  have hdescent : baseEnd_2423152 < baseStart_2423152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423171 : List Nat := [1, 1, 1, 3, 6, 1, 1, 2, 3, 3]
def baseStart_2423171 : Nat := 118140960795 + 2423171 * 2 ^ 59
def prefixEnd_2423171 : Nat := 4983230072969 + 3 ^ 40 * 2423171 * 2
def baseEnd_2423171 : Nat := 829500954024029377345697

theorem tailTrace_2423171 : CollatzResearch.WordTrace tailWord_2423171 prefixEnd_2423171 829500954024029377345697 := by
  unfold tailWord_2423171
  simp only [CollatzResearch.WordTrace]
  refine ⟨88380307104272786504053367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58920204736181857669368911 88380307104272786504053367)
  ·
    refine ⟨132570460656409179756080051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88380307104272786504053367 132570460656409179756080051)
    ·
      refine ⟨198855690984613769634120077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132570460656409179756080051 198855690984613769634120077)
      ·
        refine ⟨74570884119230163612795029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198855690984613769634120077 74570884119230163612795029)
        ·
          refine ⟨3495510193088913919349767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 74570884119230163612795029 3495510193088913919349767)
          ·
            refine ⟨5243265289633370879024651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3495510193088913919349767 5243265289633370879024651)
            ·
              refine ⟨7864897934450056318536977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5243265289633370879024651 7864897934450056318536977)
              ·
                refine ⟨5898673450837542238902733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7864897934450056318536977 5898673450837542238902733)
                ·
                  refine ⟨2212002544064078339588525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5898673450837542238902733 2212002544064078339588525)
                  ·
                    refine ⟨829500954024029377345697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2212002544064078339588525 829500954024029377345697)
                    ·
                      rfl

theorem cell22_2423171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 3, 3].length) (baseStart_2423171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2423171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2423171 prefixEnd_2423171 := by exact prefixLift 2423171
  have htrace : WordTrace (prefixWord ++ tailWord_2423171) baseStart_2423171 baseEnd_2423171 := by
    simpa [prefixWord, tailWord_2423171, baseEnd_2423171] using wordTrace_append hprefix tailTrace_2423171
  have hstable : (prefixWord ++ tailWord_2423171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423171).length < 2 ^ (prefixWord ++ tailWord_2423171).sum := by decide
  have hdescent : baseEnd_2423171 < baseStart_2423171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423201 : List Nat := [1, 2, 3, 5, 1, 1, 1, 1, 7]
def baseStart_2423201 : Nat := 118140960795 + 2423201 * 2 ^ 59
def prefixEnd_2423201 : Nat := 4983230072969 + 3 ^ 40 * 2423201 * 2
def baseEnd_2423201 : Nat := 276503741212373099698535

theorem tailTrace_2423201 : CollatzResearch.WordTrace tailWord_2423201 prefixEnd_2423201 276503741212373099698535 := by
  unfold tailWord_2423201
  simp only [CollatzResearch.WordTrace]
  refine ⟨88381401294164101627645457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58920934196109401085096971 88381401294164101627645457)
  ·
    refine ⟨66286050970623076220734093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88381401294164101627645457 66286050970623076220734093)
    ·
      refine ⟨24857269113983653582775285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66286050970623076220734093 24857269113983653582775285)
      ·
        refine ⟨2330368979435967523385183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24857269113983653582775285 2330368979435967523385183)
        ·
          refine ⟨3495553469153951285077775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2330368979435967523385183 3495553469153951285077775)
          ·
            refine ⟨5243330203730926927616663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3495553469153951285077775 5243330203730926927616663)
            ·
              refine ⟨7864995305596390391424995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5243330203730926927616663 7864995305596390391424995)
              ·
                refine ⟨11797492958394585587137493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7864995305596390391424995 11797492958394585587137493)
                ·
                  refine ⟨276503741212373099698535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11797492958394585587137493 276503741212373099698535)
                  ·
                    rfl

theorem cell22_2423201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 7].length) (baseStart_2423201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2423201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2423201 prefixEnd_2423201 := by exact prefixLift 2423201
  have htrace : WordTrace (prefixWord ++ tailWord_2423201) baseStart_2423201 baseEnd_2423201 := by
    simpa [prefixWord, tailWord_2423201, baseEnd_2423201] using wordTrace_append hprefix tailTrace_2423201
  have hstable : (prefixWord ++ tailWord_2423201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423201).length < 2 ^ (prefixWord ++ tailWord_2423201).sum := by decide
  have hdescent : baseEnd_2423201 < baseStart_2423201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423227 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 7, 5]
def baseStart_2423227 : Nat := 118140960795 + 2423227 * 2 ^ 59
def prefixEnd_2423227 : Nat := 4983230072969 + 3 ^ 40 * 2423227 * 2
def baseEnd_2423227 : Nat := 829520123968463897945525

theorem tailTrace_2423227 : CollatzResearch.WordTrace tailWord_2423227 prefixEnd_2423227 829520123968463897945525 := by
  unfold tailWord_2423227
  simp only [CollatzResearch.WordTrace]
  refine ⟨88382349592069908068091935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58921566394713272045394623 88382349592069908068091935)
  ·
    refine ⟨132573524388104862102137903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88382349592069908068091935 132573524388104862102137903)
    ·
      refine ⟨198860286582157293153206855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132573524388104862102137903 198860286582157293153206855)
      ·
        refine ⟨298290429873235939729810283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198860286582157293153206855 298290429873235939729810283)
        ·
          refine ⟨447435644809853909594715425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298290429873235939729810283 447435644809853909594715425)
          ·
            refine ⟨335576733607390432196036569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 447435644809853909594715425 335576733607390432196036569)
            ·
              refine ⟨251682550205542824147027427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 335576733607390432196036569 251682550205542824147027427)
              ·
                refine ⟨377523825308314236220541141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 251682550205542824147027427 377523825308314236220541141)
                ·
                  refine ⟨8848214655663614911418933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 377523825308314236220541141 8848214655663614911418933)
                  ·
                    refine ⟨829520123968463897945525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8848214655663614911418933 829520123968463897945525)
                    ·
                      rfl

theorem cell22_2423227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 5].length) (baseStart_2423227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2423227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2423227 prefixEnd_2423227 := by exact prefixLift 2423227
  have htrace : WordTrace (prefixWord ++ tailWord_2423227) baseStart_2423227 baseEnd_2423227 := by
    simpa [prefixWord, tailWord_2423227, baseEnd_2423227] using wordTrace_append hprefix tailTrace_2423227
  have hstable : (prefixWord ++ tailWord_2423227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423227).length < 2 ^ (prefixWord ++ tailWord_2423227).sum := by decide
  have hdescent : baseEnd_2423227 < baseStart_2423227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423229 : List Nat := [1, 4, 1, 2, 2, 2, 2, 2, 6]
def baseStart_2423229 : Nat := 118140960795 + 2423229 * 2 ^ 59
def prefixEnd_2423229 : Nat := 4983230072969 + 3 ^ 40 * 2423229 * 2
def baseEnd_2423229 : Nat := 276506936203112186465173

theorem tailTrace_2423229 : CollatzResearch.WordTrace tailWord_2423229 prefixEnd_2423229 276506936203112186465173 := by
  unfold tailWord_2423229
  simp only [CollatzResearch.WordTrace]
  refine ⟨88382422538062662409664741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58921615025375108273109827 88382422538062662409664741)
  ·
    refine ⟨16571704225886749201812139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88382422538062662409664741 16571704225886749201812139)
    ·
      refine ⟨24857556338830123802718209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16571704225886749201812139 24857556338830123802718209)
      ·
        refine ⟨18643167254122592852038657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24857556338830123802718209 18643167254122592852038657)
        ·
          refine ⟨13982375440591944639028993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18643167254122592852038657 13982375440591944639028993)
          ·
            refine ⟨10486781580443958479271745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13982375440591944639028993 10486781580443958479271745)
            ·
              refine ⟨7865086185332968859453809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10486781580443958479271745 7865086185332968859453809)
              ·
                refine ⟨5898814638999726644590357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7865086185332968859453809 5898814638999726644590357)
                ·
                  refine ⟨276506936203112186465173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5898814638999726644590357 276506936203112186465173)
                  ·
                    rfl

theorem cell22_2423229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_2423229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2423229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2423229 prefixEnd_2423229 := by exact prefixLift 2423229
  have htrace : WordTrace (prefixWord ++ tailWord_2423229) baseStart_2423229 baseEnd_2423229 := by
    simpa [prefixWord, tailWord_2423229, baseEnd_2423229] using wordTrace_append hprefix tailTrace_2423229
  have hstable : (prefixWord ++ tailWord_2423229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423229).length < 2 ^ (prefixWord ++ tailWord_2423229).sum := by decide
  have hdescent : baseEnd_2423229 < baseStart_2423229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423261 : List Nat := [1, 4, 3, 1, 1, 1, 1, 3, 4, 3]
def baseStart_2423261 : Nat := 118140960795 + 2423261 * 2 ^ 59
def prefixEnd_2423261 : Nat := 4983230072969 + 3 ^ 40 * 2423261 * 2
def baseEnd_2423261 : Nat := 829531762863299142595421

theorem tailTrace_2423261 : CollatzResearch.WordTrace tailWord_2423261 prefixEnd_2423261 829531762863299142595421 := by
  unfold tailWord_2423261
  simp only [CollatzResearch.WordTrace]
  refine ⟨88383589673946731874829637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58922393115964487916553091 88383589673946731874829637)
  ·
    refine ⟨16571923063865012226530557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88383589673946731874829637 16571923063865012226530557)
    ·
      refine ⟨6214471148949379584948959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16571923063865012226530557 6214471148949379584948959)
      ·
        refine ⟨9321706723424069377423439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6214471148949379584948959 9321706723424069377423439)
        ·
          refine ⟨13982560085136104066135159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9321706723424069377423439 13982560085136104066135159)
          ·
            refine ⟨20973840127704156099202739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13982560085136104066135159 20973840127704156099202739)
            ·
              refine ⟨31460760191556234148804109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20973840127704156099202739 31460760191556234148804109)
              ·
                refine ⟨11797785071833587805801541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31460760191556234148804109 11797785071833587805801541)
                ·
                  refine ⟨2212084700968797713587789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11797785071833587805801541 2212084700968797713587789)
                  ·
                    refine ⟨829531762863299142595421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2212084700968797713587789 829531762863299142595421)
                    ·
                      rfl

theorem cell22_2423261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_2423261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2423261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2423261 prefixEnd_2423261 := by exact prefixLift 2423261
  have htrace : WordTrace (prefixWord ++ tailWord_2423261) baseStart_2423261 baseEnd_2423261 := by
    simpa [prefixWord, tailWord_2423261, baseEnd_2423261] using wordTrace_append hprefix tailTrace_2423261
  have hstable : (prefixWord ++ tailWord_2423261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423261).length < 2 ^ (prefixWord ++ tailWord_2423261).sum := by decide
  have hdescent : baseEnd_2423261 < baseStart_2423261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423263 : List Nat := [1, 1, 2, 3, 3, 3, 3, 2, 4]
def baseStart_2423263 : Nat := 118140960795 + 2423263 * 2 ^ 59
def prefixEnd_2423263 : Nat := 4983230072969 + 3 ^ 40 * 2423263 * 2
def baseEnd_2423263 : Nat := 276510815834723934681805

theorem tailTrace_2423263 : CollatzResearch.WordTrace tailWord_2423263 prefixEnd_2423263 276510815834723934681805 := by
  unfold tailWord_2423263
  simp only [CollatzResearch.WordTrace]
  refine ⟨88383662619939486216402443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58922441746626324144268295 88383662619939486216402443)
  ·
    refine ⟨132575493929909229324603665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88383662619939486216402443 132575493929909229324603665)
    ·
      refine ⟨99431620447431921993452749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132575493929909229324603665 99431620447431921993452749)
      ·
        refine ⟨37286857667786970747544781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99431620447431921993452749 37286857667786970747544781)
        ·
          refine ⟨13982571625420114030329293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37286857667786970747544781 13982571625420114030329293)
          ·
            refine ⟨5243464359532542761373485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13982571625420114030329293 5243464359532542761373485)
            ·
              refine ⟨1966299134824703535515057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5243464359532542761373485 1966299134824703535515057)
              ·
                refine ⟨1474724351118527651636293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1966299134824703535515057 1474724351118527651636293)
                ·
                  refine ⟨276510815834723934681805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1474724351118527651636293 276510815834723934681805)
                  ·
                    rfl

theorem cell22_2423263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 2, 4].length) (baseStart_2423263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2423263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2423263 prefixEnd_2423263 := by exact prefixLift 2423263
  have htrace : WordTrace (prefixWord ++ tailWord_2423263) baseStart_2423263 baseEnd_2423263 := by
    simpa [prefixWord, tailWord_2423263, baseEnd_2423263] using wordTrace_append hprefix tailTrace_2423263
  have hstable : (prefixWord ++ tailWord_2423263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423263).length < 2 ^ (prefixWord ++ tailWord_2423263).sum := by decide
  have hdescent : baseEnd_2423263 < baseStart_2423263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423274 : List Nat := [3, 1, 3, 1, 3, 1, 1, 9]
def baseStart_2423274 : Nat := 118140960795 + 2423274 * 2 ^ 59
def prefixEnd_2423274 : Nat := 4983230072969 + 3 ^ 40 * 2423274 * 2
def baseEnd_2423274 : Nat := 92170690336552382446709

theorem tailTrace_2423274 : CollatzResearch.WordTrace tailWord_2423274 prefixEnd_2423274 92170690336552382446709 := by
  unfold tailWord_2423274
  simp only [CollatzResearch.WordTrace]
  refine ⟨22096015955724908773763219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58922709215266423396701917 22096015955724908773763219)
  ·
    refine ⟨33144023933587363160644829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22096015955724908773763219 33144023933587363160644829)
    ·
      refine ⟨12429008975095261185241811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33144023933587363160644829 12429008975095261185241811)
      ·
        refine ⟨18643513462642891777862717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12429008975095261185241811 18643513462642891777862717)
        ·
          refine ⟨6991317548491084416698519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18643513462642891777862717 6991317548491084416698519)
          ·
            refine ⟨10486976322736626625047779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6991317548491084416698519 10486976322736626625047779)
            ·
              refine ⟨15730464484104939937571669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10486976322736626625047779 15730464484104939937571669)
              ·
                refine ⟨92170690336552382446709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15730464484104939937571669 92170690336552382446709)
                ·
                  rfl

theorem cell22_2423274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 9].length) (baseStart_2423274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2423274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2423274 prefixEnd_2423274 := by exact prefixLift 2423274
  have htrace : WordTrace (prefixWord ++ tailWord_2423274) baseStart_2423274 baseEnd_2423274 := by
    simpa [prefixWord, tailWord_2423274, baseEnd_2423274] using wordTrace_append hprefix tailTrace_2423274
  have hstable : (prefixWord ++ tailWord_2423274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423274).length < 2 ^ (prefixWord ++ tailWord_2423274).sum := by decide
  have hdescent : baseEnd_2423274 < baseStart_2423274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423278 : List Nat := [4, 1, 2, 1, 2, 3, 1, 3, 2, 3]
def baseStart_2423278 : Nat := 118140960795 + 2423278 * 2 ^ 59
def prefixEnd_2423278 : Nat := 4983230072969 + 3 ^ 40 * 2423278 * 2
def baseEnd_2423278 : Nat := 829537582310716764920369

theorem tailTrace_2423278 : CollatzResearch.WordTrace tailWord_2423278 prefixEnd_2423278 829537582310716764920369 := by
  unfold tailWord_2423278
  simp only [CollatzResearch.WordTrace]
  refine ⟨11048026214360642972274811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58922806476590095852132325 11048026214360642972274811)
  ·
    refine ⟨16572039321540964458412217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11048026214360642972274811 16572039321540964458412217)
    ·
      refine ⟨12429029491155723343809163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16572039321540964458412217 12429029491155723343809163)
      ·
        refine ⟨18643544236733585015713745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12429029491155723343809163 18643544236733585015713745)
        ·
          refine ⟨13982658177550188761785309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18643544236733585015713745 13982658177550188761785309)
          ·
            refine ⟨5243496816581320785669491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13982658177550188761785309 5243496816581320785669491)
            ·
              refine ⟨7865245224871981178504237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5243496816581320785669491 7865245224871981178504237)
              ·
                refine ⟨2949466959326992941939089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7865245224871981178504237 2949466959326992941939089)
                ·
                  refine ⟨2212100219495244706454317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2949466959326992941939089 2212100219495244706454317)
                  ·
                    refine ⟨829537582310716764920369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2212100219495244706454317 829537582310716764920369)
                    ·
                      rfl

theorem cell22_2423278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_2423278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2423278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2423278 prefixEnd_2423278 := by exact prefixLift 2423278
  have htrace : WordTrace (prefixWord ++ tailWord_2423278) baseStart_2423278 baseEnd_2423278 := by
    simpa [prefixWord, tailWord_2423278, baseEnd_2423278] using wordTrace_append hprefix tailTrace_2423278
  have hstable : (prefixWord ++ tailWord_2423278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423278).length < 2 ^ (prefixWord ++ tailWord_2423278).sum := by decide
  have hdescent : baseEnd_2423278 < baseStart_2423278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423400 : List Nat := [2, 1, 4, 3, 2, 1, 2, 2, 1, 4]
def baseStart_2423400 : Nat := 118140960795 + 2423400 * 2 ^ 59
def prefixEnd_2423400 : Nat := 4983230072969 + 3 ^ 40 * 2423400 * 2
def baseEnd_2423400 : Nat := 829579345403949113369995

theorem tailTrace_2423400 : CollatzResearch.WordTrace tailWord_2423400 prefixEnd_2423400 829579345403949113369995 := by
  unfold tailWord_2423400
  simp only [CollatzResearch.WordTrace]
  refine ⟨44194329710221579307069827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58925772946962105742759769 44194329710221579307069827)
  ·
    refine ⟨66291494565332368960604741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44194329710221579307069827 66291494565332368960604741)
    ·
      refine ⟨12429655230999819180113389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66291494565332368960604741 12429655230999819180113389)
      ·
        refine ⟨4661120711624932192542521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12429655230999819180113389 4661120711624932192542521)
        ·
          refine ⟨3495840533718699144406891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4661120711624932192542521 3495840533718699144406891)
          ·
            refine ⟨5243760800578048716610337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3495840533718699144406891 5243760800578048716610337)
            ·
              refine ⟨3932820600433536537457753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5243760800578048716610337 3932820600433536537457753)
              ·
                refine ⟨2949615450325152403093315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3932820600433536537457753 2949615450325152403093315)
                ·
                  refine ⟨4424423175487728604639973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2949615450325152403093315 4424423175487728604639973)
                  ·
                    refine ⟨829579345403949113369995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4424423175487728604639973 829579345403949113369995)
                    ·
                      rfl

theorem cell22_2423400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_2423400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2423400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2423400 prefixEnd_2423400 := by exact prefixLift 2423400
  have htrace : WordTrace (prefixWord ++ tailWord_2423400) baseStart_2423400 baseEnd_2423400 := by
    simpa [prefixWord, tailWord_2423400, baseEnd_2423400] using wordTrace_append hprefix tailTrace_2423400
  have hstable : (prefixWord ++ tailWord_2423400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423400).length < 2 ^ (prefixWord ++ tailWord_2423400).sum := by decide
  have hdescent : baseEnd_2423400 < baseStart_2423400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423428 : List Nat := [2, 3, 2, 1, 3, 2, 1, 2, 2, 4]
def baseStart_2423428 : Nat := 118140960795 + 2423428 * 2 ^ 59
def prefixEnd_2423428 : Nat := 4983230072969 + 3 ^ 40 * 2423428 * 2
def baseEnd_2423428 : Nat := 829588930376166373669909

theorem tailTrace_2423428 : CollatzResearch.WordTrace tailWord_2423428 prefixEnd_2423428 829588930376166373669909 := by
  unfold tailWord_2423428
  simp only [CollatzResearch.WordTrace]
  refine ⟨44194840332170859698079469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58926453776227812930772625 44194840332170859698079469)
  ·
    refine ⟨16573065124564072386779801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44194840332170859698079469 16573065124564072386779801)
    ·
      refine ⟨12429798843423054290084851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16573065124564072386779801 12429798843423054290084851)
      ·
        refine ⟨18644698265134581435127277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12429798843423054290084851 18644698265134581435127277)
        ·
          refine ⟨6991761849425468038172729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18644698265134581435127277 6991761849425468038172729)
          ·
            refine ⟨5243821387069101028629547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6991761849425468038172729 5243821387069101028629547)
            ·
              refine ⟨7865732080603651542944321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5243821387069101028629547 7865732080603651542944321)
              ·
                refine ⟨5899299060452738657208241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7865732080603651542944321 5899299060452738657208241)
                ·
                  refine ⟨4424474295339553992906181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5899299060452738657208241 4424474295339553992906181)
                  ·
                    refine ⟨829588930376166373669909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4424474295339553992906181 829588930376166373669909)
                    ·
                      rfl

theorem cell22_2423428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_2423428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2423428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2423428 prefixEnd_2423428 := by exact prefixLift 2423428
  have htrace : WordTrace (prefixWord ++ tailWord_2423428) baseStart_2423428 baseEnd_2423428 := by
    simpa [prefixWord, tailWord_2423428, baseEnd_2423428] using wordTrace_append hprefix tailTrace_2423428
  have hstable : (prefixWord ++ tailWord_2423428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423428).length < 2 ^ (prefixWord ++ tailWord_2423428).sum := by decide
  have hdescent : baseEnd_2423428 < baseStart_2423428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423439 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 1, 8]
def baseStart_2423439 : Nat := 118140960795 + 2423439 * 2 ^ 59
def prefixEnd_2423439 : Nat := 4983230072969 + 3 ^ 40 * 2423439 * 2
def baseEnd_2423439 : Nat := 829592695900966011644875

theorem tailTrace_2423439 : CollatzResearch.WordTrace tailWord_2423439 prefixEnd_2423439 829592695900966011644875 := by
  unfold tailWord_2423439
  simp only [CollatzResearch.WordTrace]
  refine ⟨88390081867301868274809371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58926721244867912183206247 88390081867301868274809371)
  ·
    refine ⟨132585122800952802412214057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88390081867301868274809371 132585122800952802412214057)
    ·
      refine ⟨99438842100714601809160543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132585122800952802412214057 99438842100714601809160543)
      ·
        refine ⟨149158263151071902713740815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99438842100714601809160543 149158263151071902713740815)
        ·
          refine ⟨223737394726607854070611223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149158263151071902713740815 223737394726607854070611223)
          ·
            refine ⟨335606092089911781105916835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223737394726607854070611223 335606092089911781105916835)
            ·
              refine ⟨503409138134867671658875253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335606092089911781105916835 503409138134867671658875253)
              ·
                refine ⟨47194606700143844218019555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 503409138134867671658875253 47194606700143844218019555)
                ·
                  refine ⟨70791910050215766327029333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47194606700143844218019555 70791910050215766327029333)
                  ·
                    refine ⟨829592695900966011644875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 70791910050215766327029333 829592695900966011644875)
                    ·
                      rfl

theorem cell22_2423439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 8].length) (baseStart_2423439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2423439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2423439 prefixEnd_2423439 := by exact prefixLift 2423439
  have htrace : WordTrace (prefixWord ++ tailWord_2423439) baseStart_2423439 baseEnd_2423439 := by
    simpa [prefixWord, tailWord_2423439, baseEnd_2423439] using wordTrace_append hprefix tailTrace_2423439
  have hstable : (prefixWord ++ tailWord_2423439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423439).length < 2 ^ (prefixWord ++ tailWord_2423439).sum := by decide
  have hdescent : baseEnd_2423439 < baseStart_2423439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423488 : List Nat := [2, 1, 1, 2, 4, 3, 2, 2, 5]
def baseStart_2423488 : Nat := 118140960795 + 2423488 * 2 ^ 59
def prefixEnd_2423488 : Nat := 4983230072969 + 3 ^ 40 * 2423488 * 2
def baseEnd_2423488 : Nat := 276536489867448739056575

theorem tailTrace_2423488 : CollatzResearch.WordTrace tailWord_2423488 prefixEnd_2423488 276536489867448739056575 := by
  unfold tailWord_2423488
  simp only [CollatzResearch.WordTrace]
  refine ⟨44195934522062174821671559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58927912696082899762228745 44195934522062174821671559)
  ·
    refine ⟨66293901783093262232507339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44195934522062174821671559 66293901783093262232507339)
    ·
      refine ⟨99440852674639893348761009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66293901783093262232507339 99440852674639893348761009)
      ·
        refine ⟨74580639505979920011570757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99440852674639893348761009 74580639505979920011570757)
        ·
          refine ⟨13983869907371235002169517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74580639505979920011570757 13983869907371235002169517)
          ·
            refine ⟨5243951215264213125813569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13983869907371235002169517 5243951215264213125813569)
            ·
              refine ⟨3932963411448159844360177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5243951215264213125813569 3932963411448159844360177)
              ·
                refine ⟨2949722558586119883270133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3932963411448159844360177 2949722558586119883270133)
                ·
                  refine ⟨276536489867448739056575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2949722558586119883270133 276536489867448739056575)
                  ·
                    rfl

theorem cell22_2423488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2, 5].length) (baseStart_2423488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2423488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2423488 prefixEnd_2423488 := by exact prefixLift 2423488
  have htrace : WordTrace (prefixWord ++ tailWord_2423488) baseStart_2423488 baseEnd_2423488 := by
    simpa [prefixWord, tailWord_2423488, baseEnd_2423488] using wordTrace_append hprefix tailTrace_2423488
  have hstable : (prefixWord ++ tailWord_2423488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423488).length < 2 ^ (prefixWord ++ tailWord_2423488).sum := by decide
  have hdescent : baseEnd_2423488 < baseStart_2423488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423492 : List Nat := [2, 3, 3, 1, 1, 3, 1, 4, 1, 3]
def baseStart_2423492 : Nat := 118140960795 + 2423492 * 2 ^ 59
def prefixEnd_2423492 : Nat := 4983230072969 + 3 ^ 40 * 2423492 * 2
def baseEnd_2423492 : Nat := 829610838884091540069713

theorem tailTrace_2423492 : CollatzResearch.WordTrace tailWord_2423492 prefixEnd_2423492 829610838884091540069713 := by
  unfold tailWord_2423492
  simp only [CollatzResearch.WordTrace]
  refine ⟨44196007468054929163244365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58928009957406572217659153 44196007468054929163244365)
  ·
    refine ⟨16573502800520598436216637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44196007468054929163244365 16573502800520598436216637)
    ·
      refine ⟨6215063550195224413581239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16573502800520598436216637 6215063550195224413581239)
      ·
        refine ⟨9322595325292836620371859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6215063550195224413581239 9322595325292836620371859)
        ·
          refine ⟨13983892987939254930557789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9322595325292836620371859 13983892987939254930557789)
          ·
            refine ⟨5243959870477220598959171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13983892987939254930557789 5243959870477220598959171)
            ·
              refine ⟨7865939805715830898438757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5243959870477220598959171 7865939805715830898438757)
              ·
                refine ⟨1474863713571718293457267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7865939805715830898438757 1474863713571718293457267)
                ·
                  refine ⟨2212295570357577440185901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1474863713571718293457267 2212295570357577440185901)
                  ·
                    refine ⟨829610838884091540069713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2212295570357577440185901 829610838884091540069713)
                    ·
                      rfl

theorem cell22_2423492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_2423492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2423492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2423492 prefixEnd_2423492 := by exact prefixLift 2423492
  have htrace : WordTrace (prefixWord ++ tailWord_2423492) baseStart_2423492 baseEnd_2423492 := by
    simpa [prefixWord, tailWord_2423492, baseEnd_2423492] using wordTrace_append hprefix tailTrace_2423492
  have hstable : (prefixWord ++ tailWord_2423492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423492).length < 2 ^ (prefixWord ++ tailWord_2423492).sum := by decide
  have hdescent : baseEnd_2423492 < baseStart_2423492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423494 : List Nat := [6, 1, 2, 1, 3, 1, 1, 7]
def baseStart_2423494 : Nat := 118140960795 + 2423494 * 2 ^ 59
def prefixEnd_2423494 : Nat := 4983230072969 + 3 ^ 40 * 2423494 * 2
def baseEnd_2423494 : Nat := 92179058169440466835523

theorem tailTrace_2423494 : CollatzResearch.WordTrace tailWord_2423494 prefixEnd_2423494 92179058169440466835523 := by
  unfold tailWord_2423494
  simp only [CollatzResearch.WordTrace]
  refine ⟨2762252746315706645876923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 58928058588068408445374357 2762252746315706645876923)
  ·
    refine ⟨4143379119473559968815385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2762252746315706645876923 4143379119473559968815385)
    ·
      refine ⟨3107534339605169976611539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4143379119473559968815385 3107534339605169976611539)
      ·
        refine ⟨4661301509407754964917309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3107534339605169976611539 4661301509407754964917309)
        ·
          refine ⟨1747988066027908111843991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4661301509407754964917309 1747988066027908111843991)
          ·
            refine ⟨2621982099041862167765987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1747988066027908111843991 2621982099041862167765987)
            ·
              refine ⟨3932973148562793251648981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2621982099041862167765987 3932973148562793251648981)
              ·
                refine ⟨92179058169440466835523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3932973148562793251648981 92179058169440466835523)
                ·
                  rfl

theorem cell22_2423494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_2423494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2423494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2423494 prefixEnd_2423494 := by exact prefixLift 2423494
  have htrace : WordTrace (prefixWord ++ tailWord_2423494) baseStart_2423494 baseEnd_2423494 := by
    simpa [prefixWord, tailWord_2423494, baseEnd_2423494] using wordTrace_append hprefix tailTrace_2423494
  have hstable : (prefixWord ++ tailWord_2423494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423494).length < 2 ^ (prefixWord ++ tailWord_2423494).sum := by decide
  have hdescent : baseEnd_2423494 < baseStart_2423494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423535 : List Nat := [1, 1, 2, 1, 5, 2, 4, 1, 1, 4]
def baseStart_2423535 : Nat := 118140960795 + 2423535 * 2 ^ 59
def prefixEnd_2423535 : Nat := 4983230072969 + 3 ^ 40 * 2423535 * 2
def baseEnd_2423535 : Nat := 829625558662853761244581

theorem tailTrace_2423535 : CollatzResearch.WordTrace tailWord_2423535 prefixEnd_2423535 829625558662853761244581 := by
  unfold tailWord_2423535
  simp only [CollatzResearch.WordTrace]
  refine ⟨88393583274954076670304059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58929055516636051113536039 88393583274954076670304059)
  ·
    refine ⟨132590374912431115005456089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88393583274954076670304059 132590374912431115005456089)
    ·
      refine ⟨99442781184323336254092067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132590374912431115005456089 99442781184323336254092067)
      ·
        refine ⟨149164171776485004381138101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99442781184323336254092067 149164171776485004381138101)
        ·
          refine ⟨13984141104045469160731697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 149164171776485004381138101 13984141104045469160731697)
          ·
            refine ⟨10488105828034101870548773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13984141104045469160731697 10488105828034101870548773)
            ·
              refine ⟨1966519842756394100727895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10488105828034101870548773 1966519842756394100727895)
              ·
                refine ⟨2949779764134591151091843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1966519842756394100727895 2949779764134591151091843)
                ·
                  refine ⟨4424669646201886726637765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2949779764134591151091843 4424669646201886726637765)
                  ·
                    refine ⟨829625558662853761244581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4424669646201886726637765 829625558662853761244581)
                    ·
                      rfl

theorem cell22_2423535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 1, 1, 4].length) (baseStart_2423535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2423535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2423535 prefixEnd_2423535 := by exact prefixLift 2423535
  have htrace : WordTrace (prefixWord ++ tailWord_2423535) baseStart_2423535 baseEnd_2423535 := by
    simpa [prefixWord, tailWord_2423535, baseEnd_2423535] using wordTrace_append hprefix tailTrace_2423535
  have hstable : (prefixWord ++ tailWord_2423535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423535).length < 2 ^ (prefixWord ++ tailWord_2423535).sum := by decide
  have hdescent : baseEnd_2423535 < baseStart_2423535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423550 : List Nat := [4, 2, 2, 1, 2, 2, 2, 1, 6]
def baseStart_2423550 : Nat := 118140960795 + 2423550 * 2 ^ 59
def prefixEnd_2423550 : Nat := 4983230072969 + 3 ^ 40 * 2423550 * 2
def baseEnd_2423550 : Nat := 276543564489799574039845

theorem tailTrace_2423550 : CollatzResearch.WordTrace tailWord_2423550 prefixEnd_2423550 276543564489799574039845 := by
  unfold tailWord_2423550
  simp only [CollatzResearch.WordTrace]
  refine ⟨11049266296237466779012513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58929420246599822821400069 11049266296237466779012513)
  ·
    refine ⟨8286949722178100084259385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11049266296237466779012513 8286949722178100084259385)
    ·
      refine ⟨6215212291633575063194539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8286949722178100084259385 6215212291633575063194539)
      ·
        refine ⟨9322818437450362594791809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6215212291633575063194539 9322818437450362594791809)
        ·
          refine ⟨6992113828087771946093857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9322818437450362594791809 6992113828087771946093857)
          ·
            refine ⟨5244085371065828959570393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6992113828087771946093857 5244085371065828959570393)
            ·
              refine ⟨3933064028299371719677795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5244085371065828959570393 3933064028299371719677795)
              ·
                refine ⟨5899596042449057579516693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3933064028299371719677795 5899596042449057579516693)
                ·
                  refine ⟨276543564489799574039845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5899596042449057579516693 276543564489799574039845)
                  ·
                    rfl

theorem cell22_2423550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_2423550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2423550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2423550 prefixEnd_2423550 := by exact prefixLift 2423550
  have htrace : WordTrace (prefixWord ++ tailWord_2423550) baseStart_2423550 baseEnd_2423550 := by
    simpa [prefixWord, tailWord_2423550, baseEnd_2423550] using wordTrace_append hprefix tailTrace_2423550
  have hstable : (prefixWord ++ tailWord_2423550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423550).length < 2 ^ (prefixWord ++ tailWord_2423550).sum := by decide
  have hdescent : baseEnd_2423550 < baseStart_2423550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423576 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 1, 9]
def baseStart_2423576 : Nat := 118140960795 + 2423576 * 2 ^ 59
def prefixEnd_2423576 : Nat := 4983230072969 + 3 ^ 40 * 2423576 * 2
def baseEnd_2423576 : Nat := 829639593800743320969455

theorem tailTrace_2423576 : CollatzResearch.WordTrace tailWord_2423576 prefixEnd_2423576 829639593800743320969455 := by
  unfold tailWord_2423576
  simp only [CollatzResearch.WordTrace]
  refine ⟨44197539333902770336273291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58930052445203693781697721 44197539333902770336273291)
  ·
    refine ⟨66296309000854155504409937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44197539333902770336273291 66296309000854155504409937)
    ·
      refine ⟨49722231750640616628307453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66296309000854155504409937 49722231750640616628307453)
      ·
        refine ⟨18645836906490231235615295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49722231750640616628307453 18645836906490231235615295)
        ·
          refine ⟨27968755359735346853422943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18645836906490231235615295 27968755359735346853422943)
          ·
            refine ⟨41953133039603020280134415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27968755359735346853422943 41953133039603020280134415)
            ·
              refine ⟨62929699559404530420201623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41953133039603020280134415 62929699559404530420201623)
              ·
                refine ⟨94394549339106795630302435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62929699559404530420201623 94394549339106795630302435)
                ·
                  refine ⟨141591824008660193445453653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94394549339106795630302435 141591824008660193445453653)
                  ·
                    refine ⟨829639593800743320969455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 141591824008660193445453653 829639593800743320969455)
                    ·
                      rfl

theorem cell22_2423576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_2423576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2423576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2423576 prefixEnd_2423576 := by exact prefixLift 2423576
  have htrace : WordTrace (prefixWord ++ tailWord_2423576) baseStart_2423576 baseEnd_2423576 := by
    simpa [prefixWord, tailWord_2423576, baseEnd_2423576] using wordTrace_append hprefix tailTrace_2423576
  have hstable : (prefixWord ++ tailWord_2423576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423576).length < 2 ^ (prefixWord ++ tailWord_2423576).sum := by decide
  have hdescent : baseEnd_2423576 < baseStart_2423576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423700 : List Nat := [2, 4, 2, 1, 1, 1, 1, 4, 1, 5]
def baseStart_2423700 : Nat := 118140960795 + 2423700 * 2 ^ 59
def prefixEnd_2423700 : Nat := 4983230072969 + 3 ^ 40 * 2423700 * 2
def baseEnd_2423700 : Nat := 829682041534848330869075

theorem tailTrace_2423700 : CollatzResearch.WordTrace tailWord_2423700 prefixEnd_2423700 829682041534848330869075 := by
  unfold tailWord_2423700
  simp only [CollatzResearch.WordTrace]
  refine ⟨44199800659678154925030277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58933067546237539900040369 44199800659678154925030277)
  ·
    refine ⟨8287462623689654048443177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44199800659678154925030277 8287462623689654048443177)
    ·
      refine ⟨6215596967767240536332383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8287462623689654048443177 6215596967767240536332383)
      ·
        refine ⟨9323395451650860804498575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6215596967767240536332383 9323395451650860804498575)
        ·
          refine ⟨13985093177476291206747863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9323395451650860804498575 13985093177476291206747863)
          ·
            refine ⟨20977639766214436810121795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13985093177476291206747863 20977639766214436810121795)
            ·
              refine ⟨31466459649321655215182693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20977639766214436810121795 31466459649321655215182693)
              ·
                refine ⟨5899961184247810352846755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31466459649321655215182693 5899961184247810352846755)
                ·
                  refine ⟨8849941776371715529270133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5899961184247810352846755 8849941776371715529270133)
                  ·
                    refine ⟨829682041534848330869075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8849941776371715529270133 829682041534848330869075)
                    ·
                      rfl

theorem cell22_2423700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_2423700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2423700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2423700 prefixEnd_2423700 := by exact prefixLift 2423700
  have htrace : WordTrace (prefixWord ++ tailWord_2423700) baseStart_2423700 baseEnd_2423700 := by
    simpa [prefixWord, tailWord_2423700, baseEnd_2423700] using wordTrace_append hprefix tailTrace_2423700
  have hstable : (prefixWord ++ tailWord_2423700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423700).length < 2 ^ (prefixWord ++ tailWord_2423700).sum := by decide
  have hdescent : baseEnd_2423700 < baseStart_2423700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423732 : List Nat := [2, 5, 2, 1, 1, 1, 1, 2, 1, 6]
def baseStart_2423732 : Nat := 118140960795 + 2423732 * 2 ^ 59
def prefixEnd_2423732 : Nat := 4983230072969 + 3 ^ 40 * 2423732 * 2
def baseEnd_2423732 : Nat := 829692995788810914068977

theorem tailTrace_2423732 : CollatzResearch.WordTrace tailWord_2423732 prefixEnd_2423732 829692995788810914068977 := by
  unfold tailWord_2423732
  simp only [CollatzResearch.WordTrace]
  refine ⟨44200384227620189657612725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58933845636826919543483633 44200384227620189657612725)
  ·
    refine ⟨4143786021339392780401193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44200384227620189657612725 4143786021339392780401193)
    ·
      refine ⟨3107839516004544585300895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4143786021339392780401193 3107839516004544585300895)
      ·
        refine ⟨4661759274006816877951343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3107839516004544585300895 4661759274006816877951343)
        ·
          refine ⟨6992638911010225316927015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4661759274006816877951343 6992638911010225316927015)
          ·
            refine ⟨10488958366515337975390523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6992638911010225316927015 10488958366515337975390523)
            ·
              refine ⟨15733437549773006963085785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10488958366515337975390523 15733437549773006963085785)
              ·
                refine ⟨11800078162329755222314339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15733437549773006963085785 11800078162329755222314339)
                ·
                  refine ⟨17700117243494632833471509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11800078162329755222314339 17700117243494632833471509)
                  ·
                    refine ⟨829692995788810914068977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17700117243494632833471509 829692995788810914068977)
                    ·
                      rfl

theorem cell22_2423732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_2423732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2423732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2423732 prefixEnd_2423732 := by exact prefixLift 2423732
  have htrace : WordTrace (prefixWord ++ tailWord_2423732) baseStart_2423732 baseEnd_2423732 := by
    simpa [prefixWord, tailWord_2423732, baseEnd_2423732] using wordTrace_append hprefix tailTrace_2423732
  have hstable : (prefixWord ++ tailWord_2423732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423732).length < 2 ^ (prefixWord ++ tailWord_2423732).sum := by decide
  have hdescent : baseEnd_2423732 < baseStart_2423732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423788 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 1, 10]
def baseStart_2423788 : Nat := 118140960795 + 2423788 * 2 ^ 59
def prefixEnd_2423788 : Nat := 4983230072969 + 3 ^ 40 * 2423788 * 2
def baseEnd_2423788 : Nat := 829712165733245434668805

theorem tailTrace_2423788 : CollatzResearch.WordTrace tailWord_2423788 prefixEnd_2423788 829712165733245434668805 := by
  unfold tailWord_2423788
  simp only [CollatzResearch.WordTrace]
  refine ⟨44201405471518750439632009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58935207295358333919509345 44201405471518750439632009)
  ·
    refine ⟨33151054103639062829724007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44201405471518750439632009 33151054103639062829724007)
    ·
      refine ⟨49726581155458594244586011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33151054103639062829724007 49726581155458594244586011)
      ·
        refine ⟨74589871733187891366879017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49726581155458594244586011 74589871733187891366879017)
        ·
          refine ⟨55942403799890918525159263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74589871733187891366879017 55942403799890918525159263)
          ·
            refine ⟨83913605699836377787738895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55942403799890918525159263 83913605699836377787738895)
            ·
              refine ⟨125870408549754566681608343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83913605699836377787738895 125870408549754566681608343)
              ·
                refine ⟨188805612824631850022412515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125870408549754566681608343 188805612824631850022412515)
                ·
                  refine ⟨283208419236947775033618773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 188805612824631850022412515 283208419236947775033618773)
                  ·
                    refine ⟨829712165733245434668805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 283208419236947775033618773 829712165733245434668805)
                    ·
                      rfl

theorem cell22_2423788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_2423788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2423788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2423788 prefixEnd_2423788 := by exact prefixLift 2423788
  have htrace : WordTrace (prefixWord ++ tailWord_2423788) baseStart_2423788 baseEnd_2423788 := by
    simpa [prefixWord, tailWord_2423788, baseEnd_2423788] using wordTrace_append hprefix tailTrace_2423788
  have hstable : (prefixWord ++ tailWord_2423788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423788).length < 2 ^ (prefixWord ++ tailWord_2423788).sum := by decide
  have hdescent : baseEnd_2423788 < baseStart_2423788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423803 : List Nat := [1, 1, 1, 1, 1, 3, 3, 3, 8]
def baseStart_2423803 : Nat := 118140960795 + 2423803 * 2 ^ 59
def prefixEnd_2423803 : Nat := 4983230072969 + 3 ^ 40 * 2423803 * 2
def baseEnd_2423803 : Nat := 276572433513263465181253

theorem tailTrace_2423803 : CollatzResearch.WordTrace tailWord_2423803 prefixEnd_2423803 276572433513263465181253 := by
  unfold tailWord_2423803
  simp only [CollatzResearch.WordTrace]
  refine ⟨88403358037983158441060063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58935572025322105627373375 88403358037983158441060063)
  ·
    refine ⟨132605037056974737661590095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88403358037983158441060063 132605037056974737661590095)
    ·
      refine ⟨198907555585462106492385143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132605037056974737661590095 198907555585462106492385143)
      ·
        refine ⟨298361333378193159738577715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198907555585462106492385143 298361333378193159738577715)
        ·
          refine ⟨447542000067289739607866573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298361333378193159738577715 447542000067289739607866573)
          ·
            refine ⟨167828250025233652352949965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 447542000067289739607866573 167828250025233652352949965)
            ·
              refine ⟨62935593759462619632356237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 167828250025233652352949965 62935593759462619632356237)
              ·
                refine ⟨23600847659798482362133589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62935593759462619632356237 23600847659798482362133589)
                ·
                  refine ⟨276572433513263465181253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23600847659798482362133589 276572433513263465181253)
                  ·
                    rfl

theorem cell22_2423803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 8].length) (baseStart_2423803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2423803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2423803 prefixEnd_2423803 := by exact prefixLift 2423803
  have htrace : WordTrace (prefixWord ++ tailWord_2423803) baseStart_2423803 baseEnd_2423803 := by
    simpa [prefixWord, tailWord_2423803, baseEnd_2423803] using wordTrace_append hprefix tailTrace_2423803
  have hstable : (prefixWord ++ tailWord_2423803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423803).length < 2 ^ (prefixWord ++ tailWord_2423803).sum := by decide
  have hdescent : baseEnd_2423803 < baseStart_2423803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423835 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 8, 3]
def baseStart_2423835 : Nat := 118140960795 + 2423835 * 2 ^ 59
def prefixEnd_2423835 : Nat := 4983230072969 + 3 ^ 40 * 2423835 * 2
def baseEnd_2423835 : Nat := 829728254793752978743661

theorem tailTrace_2423835 : CollatzResearch.WordTrace tailWord_2423835 prefixEnd_2423835 829728254793752978743661 := by
  unfold tailWord_2423835
  simp only [CollatzResearch.WordTrace]
  refine ⟨88404525173867227906224959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58936350115911485270816639 88404525173867227906224959)
  ·
    refine ⟨132606787760800841859337439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88404525173867227906224959 132606787760800841859337439)
    ·
      refine ⟨198910181641201262789006159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132606787760800841859337439 198910181641201262789006159)
      ·
        refine ⟨298365272461801894183509239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198910181641201262789006159 298365272461801894183509239)
        ·
          refine ⟨447547908692702841275263859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298365272461801894183509239 447547908692702841275263859)
          ·
            refine ⟨671321863039054261912895789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447547908692702841275263859 671321863039054261912895789)
            ·
              refine ⟨251745698639645348217335921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 671321863039054261912895789 251745698639645348217335921)
              ·
                refine ⟨188809273979734011163001941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 251745698639645348217335921 188809273979734011163001941)
                ·
                  refine ⟨2212608679450007943316429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 188809273979734011163001941 2212608679450007943316429)
                  ·
                    refine ⟨829728254793752978743661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2212608679450007943316429 829728254793752978743661)
                    ·
                      rfl

theorem cell22_2423835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 8, 3].length) (baseStart_2423835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2423835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2423835 prefixEnd_2423835 := by exact prefixLift 2423835
  have htrace : WordTrace (prefixWord ++ tailWord_2423835) baseStart_2423835 baseEnd_2423835 := by
    simpa [prefixWord, tailWord_2423835, baseEnd_2423835] using wordTrace_append hprefix tailTrace_2423835
  have hstable : (prefixWord ++ tailWord_2423835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423835).length < 2 ^ (prefixWord ++ tailWord_2423835).sum := by decide
  have hdescent : baseEnd_2423835 < baseStart_2423835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423852 : List Nat := [2, 2, 1, 1, 1, 2, 3, 5, 2, 3]
def baseStart_2423852 : Nat := 118140960795 + 2423852 * 2 ^ 59
def prefixEnd_2423852 : Nat := 4983230072969 + 3 ^ 40 * 2423852 * 2
def baseEnd_2423852 : Nat := 829734074241170601068609

theorem tailTrace_2423852 : CollatzResearch.WordTrace tailWord_2423852 prefixEnd_2423852 829734074241170601068609 := by
  unfold tailWord_2423852
  simp only [CollatzResearch.WordTrace]
  refine ⟨44202572607402819904796905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58936763476537093206395873 44202572607402819904796905)
  ·
    refine ⟨33151929455552114928597679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44202572607402819904796905 33151929455552114928597679)
    ·
      refine ⟨49727894183328172392896519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33151929455552114928597679 49727894183328172392896519)
      ·
        refine ⟨74591841274992258589344779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49727894183328172392896519 74591841274992258589344779)
        ·
          refine ⟨111887761912488387884017169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74591841274992258589344779 111887761912488387884017169)
          ·
            refine ⟨83915821434366290913012877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111887761912488387884017169 83915821434366290913012877)
            ·
              refine ⟨31468433037887359092379829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83915821434366290913012877 31468433037887359092379829)
              ·
                refine ⟨2950165597301939914910609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31468433037887359092379829 2950165597301939914910609)
                ·
                  refine ⟨2212624197976454936182957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2950165597301939914910609 2212624197976454936182957)
                  ·
                    refine ⟨829734074241170601068609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2212624197976454936182957 829734074241170601068609)
                    ·
                      rfl

theorem cell22_2423852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 3].length) (baseStart_2423852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2423852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2423852 prefixEnd_2423852 := by exact prefixLift 2423852
  have htrace : WordTrace (prefixWord ++ tailWord_2423852) baseStart_2423852 baseEnd_2423852 := by
    simpa [prefixWord, tailWord_2423852, baseEnd_2423852] using wordTrace_append hprefix tailTrace_2423852
  have hstable : (prefixWord ++ tailWord_2423852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423852).length < 2 ^ (prefixWord ++ tailWord_2423852).sum := by decide
  have hdescent : baseEnd_2423852 < baseStart_2423852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423873 : List Nat := [1, 2, 5, 1, 4, 1, 2, 1, 1, 4]
def baseStart_2423873 : Nat := 118140960795 + 2423873 * 2 ^ 59
def prefixEnd_2423873 : Nat := 4983230072969 + 3 ^ 40 * 2423873 * 2
def baseEnd_2423873 : Nat := 829741262970333546293545

theorem tailTrace_2423873 : CollatzResearch.WordTrace tailWord_2423873 prefixEnd_2423873 829741262970333546293545 := by
  unfold tailWord_2423873
  simp only [CollatzResearch.WordTrace]
  refine ⟨88405911147729560396108273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58937274098486373597405515 88405911147729560396108273)
  ·
    refine ⟨66304433360797170297081205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88405911147729560396108273 66304433360797170297081205)
    ·
      refine ⟨6216040627574734715351363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66304433360797170297081205 6216040627574734715351363)
      ·
        refine ⟨9324060941362102073027045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6216040627574734715351363 9324060941362102073027045)
        ·
          refine ⟨1748261426505394138692571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9324060941362102073027045 1748261426505394138692571)
          ·
            refine ⟨2622392139758091208038857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1748261426505394138692571 2622392139758091208038857)
            ·
              refine ⟨1966794104818568406029143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2622392139758091208038857 1966794104818568406029143)
              ·
                refine ⟨2950191157227852609043715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1966794104818568406029143 2950191157227852609043715)
                ·
                  refine ⟨4425286735841778913565573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2950191157227852609043715 4425286735841778913565573)
                  ·
                    refine ⟨829741262970333546293545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4425286735841778913565573 829741262970333546293545)
                    ·
                      rfl

theorem cell22_2423873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_2423873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2423873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2423873 prefixEnd_2423873 := by exact prefixLift 2423873
  have htrace : WordTrace (prefixWord ++ tailWord_2423873) baseStart_2423873 baseEnd_2423873 := by
    simpa [prefixWord, tailWord_2423873, baseEnd_2423873] using wordTrace_append hprefix tailTrace_2423873
  have hstable : (prefixWord ++ tailWord_2423873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423873).length < 2 ^ (prefixWord ++ tailWord_2423873).sum := by decide
  have hdescent : baseEnd_2423873 < baseStart_2423873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423914 : List Nat := [3, 1, 3, 2, 2, 1, 2, 2, 3, 3]
def baseStart_2423914 : Nat := 118140960795 + 2423914 * 2 ^ 59
def prefixEnd_2423914 : Nat := 4983230072969 + 3 ^ 40 * 2423914 * 2
def baseEnd_2423914 : Nat := 829755298108223106018419

theorem tailTrace_2423914 : CollatzResearch.WordTrace tailWord_2423914 prefixEnd_2423914 829755298108223106018419 := by
  unfold tailWord_2423914
  simp only [CollatzResearch.WordTrace]
  refine ⟨22101851635145256099587699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58938271027054016265567197 22101851635145256099587699)
  ·
    refine ⟨33152777452717884149381549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22101851635145256099587699 33152777452717884149381549)
    ·
      refine ⟨12432291544769206556018081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33152777452717884149381549 12432291544769206556018081)
      ·
        refine ⟨9324218658576904917013561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12432291544769206556018081 9324218658576904917013561)
        ·
          refine ⟨6993163993932678687760171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9324218658576904917013561 6993163993932678687760171)
          ·
            refine ⟨10489745990899018031640257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6993163993932678687760171 10489745990899018031640257)
            ·
              refine ⟨7867309493174263523730193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10489745990899018031640257 7867309493174263523730193)
              ·
                refine ⟨5900482119880697642797645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7867309493174263523730193 5900482119880697642797645)
                ·
                  refine ⟨2212680794955261616049117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5900482119880697642797645 2212680794955261616049117)
                  ·
                    refine ⟨829755298108223106018419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2212680794955261616049117 829755298108223106018419)
                    ·
                      rfl

theorem cell22_2423914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_2423914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2423914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2423914 prefixEnd_2423914 := by exact prefixLift 2423914
  have htrace : WordTrace (prefixWord ++ tailWord_2423914) baseStart_2423914 baseEnd_2423914 := by
    simpa [prefixWord, tailWord_2423914, baseEnd_2423914] using wordTrace_append hprefix tailTrace_2423914
  have hstable : (prefixWord ++ tailWord_2423914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423914).length < 2 ^ (prefixWord ++ tailWord_2423914).sum := by decide
  have hdescent : baseEnd_2423914 < baseStart_2423914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423987 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 6, 3]
def baseStart_2423987 : Nat := 118140960795 + 2423987 * 2 ^ 59
def prefixEnd_2423987 : Nat := 4983230072969 + 3 ^ 40 * 2423987 * 2
def baseEnd_2423987 : Nat := 829780287500075248943195

theorem tailTrace_2423987 : CollatzResearch.WordTrace tailWord_2423987 prefixEnd_2423987 829780287500075248943195 := by
  unfold tailWord_2423987
  simp only [CollatzResearch.WordTrace]
  refine ⟨88410069069316557865758215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58940046046211038577172143 88410069069316557865758215)
  ·
    refine ⟨132615103603974836798637323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88410069069316557865758215 132615103603974836798637323)
    ·
      refine ⟨198922655405962255197955985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132615103603974836798637323 198922655405962255197955985)
      ·
        refine ⟨149191991554471691398466989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198922655405962255197955985 149191991554471691398466989)
        ·
          refine ⟨55946996832926884274425121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149191991554471691398466989 55946996832926884274425121)
          ·
            refine ⟨41960247624695163205818841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55946996832926884274425121 41960247624695163205818841)
            ·
              refine ⟨31470185718521372404364131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41960247624695163205818841 31470185718521372404364131)
              ·
                refine ⟨47205278577782058606546197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31470185718521372404364131 47205278577782058606546197)
                ·
                  refine ⟨2212747433333533997181853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 47205278577782058606546197 2212747433333533997181853)
                  ·
                    refine ⟨829780287500075248943195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2212747433333533997181853 829780287500075248943195)
                    ·
                      rfl

theorem cell22_2423987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 6, 3].length) (baseStart_2423987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2423987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2423987 prefixEnd_2423987 := by exact prefixLift 2423987
  have htrace : WordTrace (prefixWord ++ tailWord_2423987) baseStart_2423987 baseEnd_2423987 := by
    simpa [prefixWord, tailWord_2423987, baseEnd_2423987] using wordTrace_append hprefix tailTrace_2423987
  have hstable : (prefixWord ++ tailWord_2423987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423987).length < 2 ^ (prefixWord ++ tailWord_2423987).sum := by decide
  have hdescent : baseEnd_2423987 < baseStart_2423987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424000 : List Nat := [2, 1, 1, 2, 16]
def baseStart_2424000 : Nat := 118140960795 + 2424000 * 2 ^ 59
def prefixEnd_2424000 : Nat := 4983230072969 + 3 ^ 40 * 2424000 * 2
def baseEnd_2424000 : Nat := 3414752006854928182585

theorem tailTrace_2424000 : CollatzResearch.WordTrace tailWord_2424000 prefixEnd_2424000 3414752006854928182585 := by
  unfold tailWord_2424000
  simp only [CollatzResearch.WordTrace]
  refine ⟨44205271609134730542990727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58940362145512974057320969 44205271609134730542990727)
  ·
    refine ⟨66307907413702095814486091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44205271609134730542990727 66307907413702095814486091)
    ·
      refine ⟨99461861120553143721729137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66307907413702095814486091 99461861120553143721729137)
      ·
        refine ⟨74596395840414857791296853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99461861120553143721729137 74596395840414857791296853)
        ·
          refine ⟨3414752006854928182585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 16 74596395840414857791296853 3414752006854928182585)
          ·
            rfl

theorem cell22_2424000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 16].length) (baseStart_2424000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2424000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2424000 prefixEnd_2424000 := by exact prefixLift 2424000
  have htrace : WordTrace (prefixWord ++ tailWord_2424000) baseStart_2424000 baseEnd_2424000 := by
    simpa [prefixWord, tailWord_2424000, baseEnd_2424000] using wordTrace_append hprefix tailTrace_2424000
  have hstable : (prefixWord ++ tailWord_2424000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424000).length < 2 ^ (prefixWord ++ tailWord_2424000).sum := by decide
  have hdescent : baseEnd_2424000 < baseStart_2424000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424021 : List Nat := [1, 3, 2, 4, 1, 1, 2, 3, 2, 3]
def baseStart_2424021 : Nat := 118140960795 + 2424021 * 2 ^ 59
def prefixEnd_2424021 : Nat := 4983230072969 + 3 ^ 40 * 2424021 * 2
def baseEnd_2424021 : Nat := 829791926394910493593091

theorem tailTrace_2424021 : CollatzResearch.WordTrace tailWord_2424021 prefixEnd_2424021 829791926394910493593091 := by
  unfold tailWord_2424021
  simp only [CollatzResearch.WordTrace]
  refine ⟨88411309151193381672495917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58940872767462254448330611 88411309151193381672495917)
  ·
    refine ⟨33154240931697518127185969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88411309151193381672495917 33154240931697518127185969)
    ·
      refine ⟨24865680698773138595389477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33154240931697518127185969 24865680698773138595389477)
      ·
        refine ⟨4662315131019963486635527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24865680698773138595389477 4662315131019963486635527)
        ·
          refine ⟨6993472696529945229953291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4662315131019963486635527 6993472696529945229953291)
          ·
            refine ⟨10490209044794917844929937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6993472696529945229953291 10490209044794917844929937)
            ·
              refine ⟨7867656783596188383697453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10490209044794917844929937 7867656783596188383697453)
              ·
                refine ⟨2950371293848570643886545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7867656783596188383697453 2950371293848570643886545)
                ·
                  refine ⟨2212778470386427982914909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2950371293848570643886545 2212778470386427982914909)
                  ·
                    refine ⟨829791926394910493593091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2212778470386427982914909 829791926394910493593091)
                    ·
                      rfl

theorem cell22_2424021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3, 2, 3].length) (baseStart_2424021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2424021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2424021 prefixEnd_2424021 := by exact prefixLift 2424021
  have htrace : WordTrace (prefixWord ++ tailWord_2424021) baseStart_2424021 baseEnd_2424021 := by
    simpa [prefixWord, tailWord_2424021, baseEnd_2424021] using wordTrace_append hprefix tailTrace_2424021
  have hstable : (prefixWord ++ tailWord_2424021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424021).length < 2 ^ (prefixWord ++ tailWord_2424021).sum := by decide
  have hdescent : baseEnd_2424021 < baseStart_2424021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424124 : List Nat := [2, 2, 2, 2, 1, 3, 3, 1, 6]
def baseStart_2424124 : Nat := 118140960795 + 2424124 * 2 ^ 59
def prefixEnd_2424124 : Nat := 4983230072969 + 3 ^ 40 * 2424124 * 2
def baseEnd_2424124 : Nat := 276609061799950852755925

theorem tailTrace_2424124 : CollatzResearch.WordTrace tailWord_2424124 prefixEnd_2424124 276609061799950852755925 := by
  unfold tailWord_2424124
  simp only [CollatzResearch.WordTrace]
  refine ⟨44207532934910115131747713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58943377246546820175663617 44207532934910115131747713)
  ·
    refine ⟨33155649701182586348810785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44207532934910115131747713 33155649701182586348810785)
    ·
      refine ⟨24866737275886939761608089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33155649701182586348810785 24866737275886939761608089)
      ·
        refine ⟨18650052956915204821206067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24866737275886939761608089 18650052956915204821206067)
        ·
          refine ⟨27975079435372807231809101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18650052956915204821206067 27975079435372807231809101)
          ·
            refine ⟨10490654788264802711928413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27975079435372807231809101 10490654788264802711928413)
            ·
              refine ⟨3933995545599301016973155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10490654788264802711928413 3933995545599301016973155)
              ·
                refine ⟨5900993318398951525459733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3933995545599301016973155 5900993318398951525459733)
                ·
                  refine ⟨276609061799950852755925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5900993318398951525459733 276609061799950852755925)
                  ·
                    rfl

theorem cell22_2424124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 6].length) (baseStart_2424124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2424124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2424124 prefixEnd_2424124 := by exact prefixLift 2424124
  have htrace : WordTrace (prefixWord ++ tailWord_2424124) baseStart_2424124 baseEnd_2424124 := by
    simpa [prefixWord, tailWord_2424124, baseEnd_2424124] using wordTrace_append hprefix tailTrace_2424124
  have hstable : (prefixWord ++ tailWord_2424124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424124).length < 2 ^ (prefixWord ++ tailWord_2424124).sum := by decide
  have hdescent : baseEnd_2424124 < baseStart_2424124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424137 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 3, 6]
def baseStart_2424137 : Nat := 118140960795 + 2424137 * 2 ^ 59
def prefixEnd_2424137 : Nat := 4983230072969 + 3 ^ 40 * 2424137 * 2
def baseEnd_2424137 : Nat := 829831635565524857692735

theorem tailTrace_2424137 : CollatzResearch.WordTrace tailWord_2424137 prefixEnd_2424137 829831635565524857692735 := by
  unfold tailWord_2424137
  simp only [CollatzResearch.WordTrace]
  refine ⟨88415540018773133483718665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58943693345848755655812443 88415540018773133483718665)
  ·
    refine ⟨66311655014079850112788999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88415540018773133483718665 66311655014079850112788999)
    ·
      refine ⟨99467482521119775169183499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66311655014079850112788999 99467482521119775169183499)
      ·
        refine ⟨149201223781679662753775249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99467482521119775169183499 149201223781679662753775249)
        ·
          refine ⟨111900917836259747065331437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149201223781679662753775249 111900917836259747065331437)
          ·
            refine ⟨41962844188597405149499289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111900917836259747065331437 41962844188597405149499289)
            ·
              refine ⟨31472133141448053862124467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41962844188597405149499289 31472133141448053862124467)
              ·
                refine ⟨47208199712172080793186701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31472133141448053862124467 47208199712172080793186701)
                ·
                  refine ⟨17703074892064530297445013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47208199712172080793186701 17703074892064530297445013)
                  ·
                    refine ⟨829831635565524857692735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17703074892064530297445013 829831635565524857692735)
                    ·
                      rfl

theorem cell22_2424137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 6].length) (baseStart_2424137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2424137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2424137 prefixEnd_2424137 := by exact prefixLift 2424137
  have htrace : WordTrace (prefixWord ++ tailWord_2424137) baseStart_2424137 baseEnd_2424137 := by
    simpa [prefixWord, tailWord_2424137, baseEnd_2424137] using wordTrace_append hprefix tailTrace_2424137
  have hstable : (prefixWord ++ tailWord_2424137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424137).length < 2 ^ (prefixWord ++ tailWord_2424137).sum := by decide
  have hdescent : baseEnd_2424137 < baseStart_2424137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424152 : List Nat := [2, 1, 2, 2, 1, 1, 3, 10]
def baseStart_2424152 : Nat := 118140960795 + 2424152 * 2 ^ 59
def prefixEnd_2424152 : Nat := 4983230072969 + 3 ^ 40 * 2424152 * 2
def baseEnd_2424152 : Nat := 92204085596896646507521

theorem tailTrace_2424152 : CollatzResearch.WordTrace tailWord_2424152 prefixEnd_2424152 92204085596896646507521 := by
  unfold tailWord_2424152
  simp only [CollatzResearch.WordTrace]
  refine ⟨44208043556859395522757355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58944058075812527363676473 44208043556859395522757355)
  ·
    refine ⟨66312065335289093284136033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44208043556859395522757355 66312065335289093284136033)
    ·
      refine ⟨49734049001466819963102025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66312065335289093284136033 49734049001466819963102025)
      ·
        refine ⟨37300536751100114972326519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49734049001466819963102025 37300536751100114972326519)
        ·
          refine ⟨55950805126650172458489779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37300536751100114972326519 55950805126650172458489779)
          ·
            refine ⟨83926207689975258687734669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55950805126650172458489779 83926207689975258687734669)
            ·
              refine ⟨31472327883740722007900501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83926207689975258687734669 31472327883740722007900501)
              ·
                refine ⟨92204085596896646507521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 31472327883740722007900501 92204085596896646507521)
                ·
                  rfl

theorem cell22_2424152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 10].length) (baseStart_2424152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2424152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2424152 prefixEnd_2424152 := by exact prefixLift 2424152
  have htrace : WordTrace (prefixWord ++ tailWord_2424152) baseStart_2424152 baseEnd_2424152 := by
    simpa [prefixWord, tailWord_2424152, baseEnd_2424152] using wordTrace_append hprefix tailTrace_2424152
  have hstable : (prefixWord ++ tailWord_2424152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424152).length < 2 ^ (prefixWord ++ tailWord_2424152).sum := by decide
  have hdescent : baseEnd_2424152 < baseStart_2424152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424154 : List Nat := [3, 1, 1, 2, 1, 2, 3, 3, 2, 4]
def baseStart_2424154 : Nat := 118140960795 + 2424154 * 2 ^ 59
def prefixEnd_2424154 : Nat := 4983230072969 + 3 ^ 40 * 2424154 * 2
def baseEnd_2424154 : Nat := 829837455012942480017683

theorem tailTrace_2424154 : CollatzResearch.WordTrace tailWord_2424154 prefixEnd_2424154 829837455012942480017683 := by
  unfold tailWord_2424154
  simp only [CollatzResearch.WordTrace]
  refine ⟨22104040014927886346771879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58944106706474363591391677 22104040014927886346771879)
  ·
    refine ⟨33156060022391829520157819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22104040014927886346771879 33156060022391829520157819)
    ·
      refine ⟨49734090033587744280236729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33156060022391829520157819 49734090033587744280236729)
      ·
        refine ⟨37300567525190808210177547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49734090033587744280236729 37300567525190808210177547)
        ·
          refine ⟨55950851287786212315266321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37300567525190808210177547 55950851287786212315266321)
          ·
            refine ⟨41963138465839659236449741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55950851287786212315266321 41963138465839659236449741)
            ·
              refine ⟨15736176924689872213668653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41963138465839659236449741 15736176924689872213668653)
              ·
                refine ⟨5901066346758702080125745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15736176924689872213668653 5901066346758702080125745)
                ·
                  refine ⟨4425799760069026560094309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5901066346758702080125745 4425799760069026560094309)
                  ·
                    refine ⟨829837455012942480017683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4425799760069026560094309 829837455012942480017683)
                    ·
                      rfl

theorem cell22_2424154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 2, 4].length) (baseStart_2424154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2424154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2424154 prefixEnd_2424154 := by exact prefixLift 2424154
  have htrace : WordTrace (prefixWord ++ tailWord_2424154) baseStart_2424154 baseEnd_2424154 := by
    simpa [prefixWord, tailWord_2424154, baseEnd_2424154] using wordTrace_append hprefix tailTrace_2424154
  have hstable : (prefixWord ++ tailWord_2424154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424154).length < 2 ^ (prefixWord ++ tailWord_2424154).sum := by decide
  have hdescent : baseEnd_2424154 < baseStart_2424154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424173 : List Nat := [1, 5, 1, 1, 1, 4, 2, 2, 2, 3]
def baseStart_2424173 : Nat := 118140960795 + 2424173 * 2 ^ 59
def prefixEnd_2424173 : Nat := 4983230072969 + 3 ^ 40 * 2424173 * 2
def baseEnd_2424173 : Nat := 829843959101232763792625

theorem tailTrace_2424173 : CollatzResearch.WordTrace tailWord_2424173 prefixEnd_2424173 829843959101232763792625 := by
  unfold tailWord_2424173
  simp only [CollatzResearch.WordTrace]
  refine ⟨88416853046642711632029173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58944568697761807754686115 88416853046642711632029173)
  ·
    refine ⟨8289079973122754215502735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88416853046642711632029173 8289079973122754215502735)
    ·
      refine ⟨12433619959684131323254103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8289079973122754215502735 12433619959684131323254103)
      ·
        refine ⟨18650429939526196984881155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12433619959684131323254103 18650429939526196984881155)
        ·
          refine ⟨27975644909289295477321733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18650429939526196984881155 27975644909289295477321733)
          ·
            refine ⟨5245433420491742901997825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27975644909289295477321733 5245433420491742901997825)
            ·
              refine ⟨3934075065368807176498369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5245433420491742901997825 3934075065368807176498369)
              ·
                refine ⟨2950556299026605382373777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3934075065368807176498369 2950556299026605382373777)
                ·
                  refine ⟨2212917224269954036780333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2950556299026605382373777 2212917224269954036780333)
                  ·
                    refine ⟨829843959101232763792625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2212917224269954036780333 829843959101232763792625)
                    ·
                      rfl

theorem cell22_2424173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_2424173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2424173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2424173 prefixEnd_2424173 := by exact prefixLift 2424173
  have htrace : WordTrace (prefixWord ++ tailWord_2424173) baseStart_2424173 baseEnd_2424173 := by
    simpa [prefixWord, tailWord_2424173, baseEnd_2424173] using wordTrace_append hprefix tailTrace_2424173
  have hstable : (prefixWord ++ tailWord_2424173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424173).length < 2 ^ (prefixWord ++ tailWord_2424173).sum := by decide
  have hdescent : baseEnd_2424173 < baseStart_2424173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424184 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 9, 3]
def baseStart_2424184 : Nat := 118140960795 + 2424184 * 2 ^ 59
def prefixEnd_2424184 : Nat := 4983230072969 + 3 ^ 40 * 2424184 * 2
def baseEnd_2424184 : Nat := 829847724626032401767591

theorem tailTrace_2424184 : CollatzResearch.WordTrace tailWord_2424184 prefixEnd_2424184 829847724626032401767591 := by
  unfold tailWord_2424184
  simp only [CollatzResearch.WordTrace]
  refine ⟨44208627124801430255339803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58944836166401907007119737 44208627124801430255339803)
  ·
    refine ⟨66312940687202145383009705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44208627124801430255339803 66312940687202145383009705)
    ·
      refine ⟨49734705515401609037257279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66312940687202145383009705 49734705515401609037257279)
      ·
        refine ⟨74602058273102413555885919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49734705515401609037257279 74602058273102413555885919)
        ·
          refine ⟨111903087409653620333828879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74602058273102413555885919 111903087409653620333828879)
          ·
            refine ⟨167854631114480430500743319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111903087409653620333828879 167854631114480430500743319)
            ·
              refine ⟨251781946671720645751114979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167854631114480430500743319 251781946671720645751114979)
              ·
                refine ⟨377672920007580968626672469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 251781946671720645751114979 377672920007580968626672469)
                ·
                  refine ⟨2212927265669419738046909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 377672920007580968626672469 2212927265669419738046909)
                  ·
                    refine ⟨829847724626032401767591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2212927265669419738046909 829847724626032401767591)
                    ·
                      rfl

theorem cell22_2424184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 9, 3].length) (baseStart_2424184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2424184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2424184 prefixEnd_2424184 := by exact prefixLift 2424184
  have htrace : WordTrace (prefixWord ++ tailWord_2424184) baseStart_2424184 baseEnd_2424184 := by
    simpa [prefixWord, tailWord_2424184, baseEnd_2424184] using wordTrace_append hprefix tailTrace_2424184
  have hstable : (prefixWord ++ tailWord_2424184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424184).length < 2 ^ (prefixWord ++ tailWord_2424184).sum := by decide
  have hdescent : baseEnd_2424184 < baseStart_2424184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424190 : List Nat := [4, 2, 3, 2, 1, 1, 2, 1, 1, 5]
def baseStart_2424190 : Nat := 118140960795 + 2424190 * 2 ^ 59
def prefixEnd_2424190 : Nat := 4983230072969 + 3 ^ 40 * 2424190 * 2
def baseEnd_2424190 : Nat := 829849778548650386117573

theorem tailTrace_2424190 : CollatzResearch.WordTrace tailWord_2424190 prefixEnd_2424190 829849778548650386117573 := by
  unfold tailWord_2424190
  simp only [CollatzResearch.WordTrace]
  refine ⟨11052184135947640441924753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58944982058387415690265349 11052184135947640441924753)
  ·
    refine ⟨8289138101960730331443565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11052184135947640441924753 8289138101960730331443565)
    ·
      refine ⟨3108426788235273874291337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8289138101960730331443565 3108426788235273874291337)
      ·
        refine ⟨2331320091176455405718503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3108426788235273874291337 2331320091176455405718503)
        ·
          refine ⟨3496980136764683108577755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2331320091176455405718503 3496980136764683108577755)
          ·
            refine ⟨5245470205147024662866633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3496980136764683108577755 5245470205147024662866633)
            ·
              refine ⟨3934102653860268497149975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5245470205147024662866633 3934102653860268497149975)
              ·
                refine ⟨5901153980790402745724963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3934102653860268497149975 5901153980790402745724963)
                ·
                  refine ⟨8851730971185604118587445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5901153980790402745724963 8851730971185604118587445)
                  ·
                    refine ⟨829849778548650386117573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8851730971185604118587445 829849778548650386117573)
                    ·
                      rfl

theorem cell22_2424190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_2424190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2424190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2424190 prefixEnd_2424190 := by exact prefixLift 2424190
  have htrace : WordTrace (prefixWord ++ tailWord_2424190) baseStart_2424190 baseEnd_2424190 := by
    simpa [prefixWord, tailWord_2424190, baseEnd_2424190] using wordTrace_append hprefix tailTrace_2424190
  have hstable : (prefixWord ++ tailWord_2424190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424190).length < 2 ^ (prefixWord ++ tailWord_2424190).sum := by decide
  have hdescent : baseEnd_2424190 < baseStart_2424190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424259 : List Nat := [1, 1, 1, 3, 1, 1, 6, 2, 6]
def baseStart_2424259 : Nat := 118140960795 + 2424259 * 2 ^ 59
def prefixEnd_2424259 : Nat := 4983230072969 + 3 ^ 40 * 2424259 * 2
def baseEnd_2424259 : Nat := 276624466219585735380787

theorem tailTrace_2424259 : CollatzResearch.WordTrace tailWord_2424259 prefixEnd_2424259 276624466219585735380787 := by
  unfold tailWord_2424259
  simp only [CollatzResearch.WordTrace]
  refine ⟨88419989724331148319659831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58946659816220765546439887 88419989724331148319659831)
  ·
    refine ⟨132629984586496722479489747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88419989724331148319659831 132629984586496722479489747)
    ·
      refine ⟨198944976879745083719234621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132629984586496722479489747 198944976879745083719234621)
      ·
        refine ⟨74604366329904406394712983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198944976879745083719234621 74604366329904406394712983)
        ·
          refine ⟨111906549494856609592069475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74604366329904406394712983 111906549494856609592069475)
          ·
            refine ⟨167859824242284914388104213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111906549494856609592069475 167859824242284914388104213)
            ·
              refine ⟨7868429261357105361942385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 167859824242284914388104213 7868429261357105361942385)
              ·
                refine ⟨5901321946017829021456789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7868429261357105361942385 5901321946017829021456789)
                ·
                  refine ⟨276624466219585735380787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5901321946017829021456789 276624466219585735380787)
                  ·
                    rfl

theorem cell22_2424259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 6].length) (baseStart_2424259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2424259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2424259 prefixEnd_2424259 := by exact prefixLift 2424259
  have htrace : WordTrace (prefixWord ++ tailWord_2424259) baseStart_2424259 baseEnd_2424259 := by
    simpa [prefixWord, tailWord_2424259, baseEnd_2424259] using wordTrace_append hprefix tailTrace_2424259
  have hstable : (prefixWord ++ tailWord_2424259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424259).length < 2 ^ (prefixWord ++ tailWord_2424259).sum := by decide
  have hdescent : baseEnd_2424259 < baseStart_2424259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424293 : List Nat := [1, 3, 1, 5, 1, 3, 1, 1, 6]
def baseStart_2424293 : Nat := 118140960795 + 2424293 * 2 ^ 59
def prefixEnd_2424293 : Nat := 4983230072969 + 3 ^ 40 * 2424293 * 2
def baseEnd_2424293 : Nat := 276628345851197483597419

theorem tailTrace_2424293 : CollatzResearch.WordTrace tailWord_2424293 prefixEnd_2424293 276628345851197483597419 := by
  unfold tailWord_2424293
  simp only [CollatzResearch.WordTrace]
  refine ⟨88421229806207972126397533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58947486537471981417598355 88421229806207972126397533)
  ·
    refine ⟨33157961177327989547399075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88421229806207972126397533 33157961177327989547399075)
    ·
      refine ⟨49736941765991984321098613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33157961177327989547399075 49736941765991984321098613)
      ·
        refine ⟨4662838290561748530102995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49736941765991984321098613 4662838290561748530102995)
        ·
          refine ⟨6994257435842622795154493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4662838290561748530102995 6994257435842622795154493)
          ·
            refine ⟨2622846538440983548182935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6994257435842622795154493 2622846538440983548182935)
            ·
              refine ⟨3934269807661475322274403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2622846538440983548182935 3934269807661475322274403)
              ·
                refine ⟨5901404711492212983411605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3934269807661475322274403 5901404711492212983411605)
                ·
                  refine ⟨276628345851197483597419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5901404711492212983411605 276628345851197483597419)
                  ·
                    rfl

theorem cell22_2424293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 6].length) (baseStart_2424293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2424293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2424293 prefixEnd_2424293 := by exact prefixLift 2424293
  have htrace : WordTrace (prefixWord ++ tailWord_2424293) baseStart_2424293 baseEnd_2424293 := by
    simpa [prefixWord, tailWord_2424293, baseEnd_2424293] using wordTrace_append hprefix tailTrace_2424293
  have hstable : (prefixWord ++ tailWord_2424293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424293).length < 2 ^ (prefixWord ++ tailWord_2424293).sum := by decide
  have hdescent : baseEnd_2424293 < baseStart_2424293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424304 : List Nat := [2, 1, 1, 1, 3, 4, 1, 9]
def baseStart_2424304 : Nat := 118140960795 + 2424304 * 2 ^ 59
def prefixEnd_2424304 : Nat := 4983230072969 + 3 ^ 40 * 2424304 * 2
def baseEnd_2424304 : Nat := 92209867008710232085247

theorem tailTrace_2424304 : CollatzResearch.WordTrace tailWord_2424304 prefixEnd_2424304 92209867008710232085247 := by
  unfold tailWord_2424304
  simp only [CollatzResearch.WordTrace]
  refine ⟨44210815504584060502523983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58947754006112080670031977 44210815504584060502523983)
  ·
    refine ⟨66316223256876090753785975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44210815504584060502523983 66316223256876090753785975)
    ·
      refine ⟨99474334885314136130678963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66316223256876090753785975 99474334885314136130678963)
      ·
        refine ⟨149211502327971204196018445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99474334885314136130678963 149211502327971204196018445)
        ·
          refine ⟨55954313372989201573506917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149211502327971204196018445 55954313372989201573506917)
          ·
            refine ⟨10491433757435475295032547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55954313372989201573506917 10491433757435475295032547)
            ·
              refine ⟨15737150636153212942548821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10491433757435475295032547 15737150636153212942548821)
              ·
                refine ⟨92209867008710232085247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15737150636153212942548821 92209867008710232085247)
                ·
                  rfl

theorem cell22_2424304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 9].length) (baseStart_2424304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2424304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2424304 prefixEnd_2424304 := by exact prefixLift 2424304
  have htrace : WordTrace (prefixWord ++ tailWord_2424304) baseStart_2424304 baseEnd_2424304 := by
    simpa [prefixWord, tailWord_2424304, baseEnd_2424304] using wordTrace_append hprefix tailTrace_2424304
  have hstable : (prefixWord ++ tailWord_2424304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424304).length < 2 ^ (prefixWord ++ tailWord_2424304).sum := by decide
  have hdescent : baseEnd_2424304 < baseStart_2424304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424441 : List Nat := [1, 2, 1, 3, 3, 1, 1, 3, 1, 6]
def baseStart_2424441 : Nat := 118140960795 + 2424441 * 2 ^ 59
def prefixEnd_2424441 : Nat := 4983230072969 + 3 ^ 40 * 2424441 * 2
def baseEnd_2424441 : Nat := 829935700978169398091803

theorem tailTrace_2424441 : CollatzResearch.WordTrace tailWord_2424441 prefixEnd_2424441 829935700978169398091803 := by
  unfold tailWord_2424441
  simp only [CollatzResearch.WordTrace]
  refine ⟨88426627809671793402785177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58951085206447862268523451 88426627809671793402785177)
  ·
    refine ⟨66319970857253845052088883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88426627809671793402785177 66319970857253845052088883)
    ·
      refine ⟨99479956285880767578133325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66319970857253845052088883 99479956285880767578133325)
      ·
        refine ⟨37304983607205287841799997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99479956285880767578133325 37304983607205287841799997)
        ·
          refine ⟨13989368852701982940674999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37304983607205287841799997 13989368852701982940674999)
          ·
            refine ⟨20984053279052974411012499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13989368852701982940674999 20984053279052974411012499)
            ·
              refine ⟨31476079918579461616518749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20984053279052974411012499 31476079918579461616518749)
              ·
                refine ⟨11803529969467298106194531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31476079918579461616518749 11803529969467298106194531)
                ·
                  refine ⟨17705294954200947159291797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11803529969467298106194531 17705294954200947159291797)
                  ·
                    refine ⟨829935700978169398091803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17705294954200947159291797 829935700978169398091803)
                    ·
                      rfl

theorem cell22_2424441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 6].length) (baseStart_2424441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2424441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2424441 prefixEnd_2424441 := by exact prefixLift 2424441
  have htrace : WordTrace (prefixWord ++ tailWord_2424441) baseStart_2424441 baseEnd_2424441 := by
    simpa [prefixWord, tailWord_2424441, baseEnd_2424441] using wordTrace_append hprefix tailTrace_2424441
  have hstable : (prefixWord ++ tailWord_2424441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424441).length < 2 ^ (prefixWord ++ tailWord_2424441).sum := by decide
  have hdescent : baseEnd_2424441 < baseStart_2424441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424445 : List Nat := [1, 4, 1, 1, 4, 1, 3, 3, 4]
def baseStart_2424445 : Nat := 118140960795 + 2424445 * 2 ^ 59
def prefixEnd_2424445 : Nat := 4983230072969 + 3 ^ 40 * 2424445 * 2
def baseEnd_2424445 : Nat := 276645690086638240330597

theorem tailTrace_2424445 : CollatzResearch.WordTrace tailWord_2424445 prefixEnd_2424445 276645690086638240330597 := by
  unfold tailWord_2424445
  simp only [CollatzResearch.WordTrace]
  refine ⟨88426773701657302085930789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58951182467771534723953859 88426773701657302085930789)
  ·
    refine ⟨16580020069060744141112023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88426773701657302085930789 16580020069060744141112023)
    ·
      refine ⟨24870030103591116211668035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16580020069060744141112023 24870030103591116211668035)
      ·
        refine ⟨37305045155386674317502053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24870030103591116211668035 37305045155386674317502053)
        ·
          refine ⟨6994695966635001434531635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37305045155386674317502053 6994695966635001434531635)
          ·
            refine ⟨10492043949952502151797453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6994695966635001434531635 10492043949952502151797453)
            ·
              refine ⟨3934516481232188306924045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10492043949952502151797453 3934516481232188306924045)
              ·
                refine ⟨1475443680462070615096517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3934516481232188306924045 1475443680462070615096517)
                ·
                  refine ⟨276645690086638240330597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1475443680462070615096517 276645690086638240330597)
                  ·
                    rfl

theorem cell22_2424445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 3, 4].length) (baseStart_2424445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2424445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2424445 prefixEnd_2424445 := by exact prefixLift 2424445
  have htrace : WordTrace (prefixWord ++ tailWord_2424445) baseStart_2424445 baseEnd_2424445 := by
    simpa [prefixWord, tailWord_2424445, baseEnd_2424445] using wordTrace_append hprefix tailTrace_2424445
  have hstable : (prefixWord ++ tailWord_2424445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424445).length < 2 ^ (prefixWord ++ tailWord_2424445).sum := by decide
  have hdescent : baseEnd_2424445 < baseStart_2424445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424458 : List Nat := [3, 1, 2, 3, 2, 1, 1, 1, 4, 4]
def baseStart_2424458 : Nat := 118140960795 + 2424458 * 2 ^ 59
def prefixEnd_2424458 : Nat := 4983230072969 + 3 ^ 40 * 2424458 * 2
def baseEnd_2424458 : Nat := 829941520425587020416751

theorem tailTrace_2424458 : CollatzResearch.WordTrace tailWord_2424458 prefixEnd_2424458 829941520425587020416751 := by
  unfold tailWord_2424458
  simp only [CollatzResearch.WordTrace]
  refine ⟨22106811962652551326538507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58951498567073470204102685 22106811962652551326538507)
  ·
    refine ⟨33160217943978826989807761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22106811962652551326538507 33160217943978826989807761)
    ·
      refine ⟨24870163457984120242355821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33160217943978826989807761 24870163457984120242355821)
      ·
        refine ⟨9326311296744045090883433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24870163457984120242355821 9326311296744045090883433)
        ·
          refine ⟨6994733472558033818162575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9326311296744045090883433 6994733472558033818162575)
          ·
            refine ⟨10492100208837050727243863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6994733472558033818162575 10492100208837050727243863)
            ·
              refine ⟨15738150313255576090865795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10492100208837050727243863 15738150313255576090865795)
              ·
                refine ⟨23607225469883364136298693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15738150313255576090865795 23607225469883364136298693)
                ·
                  refine ⟨4426354775603130775556005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23607225469883364136298693 4426354775603130775556005)
                  ·
                    refine ⟨829941520425587020416751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4426354775603130775556005 829941520425587020416751)
                    ·
                      rfl

theorem cell22_2424458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_2424458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2424458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2424458 prefixEnd_2424458 := by exact prefixLift 2424458
  have htrace : WordTrace (prefixWord ++ tailWord_2424458) baseStart_2424458 baseEnd_2424458 := by
    simpa [prefixWord, tailWord_2424458, baseEnd_2424458] using wordTrace_append hprefix tailTrace_2424458
  have hstable : (prefixWord ++ tailWord_2424458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424458).length < 2 ^ (prefixWord ++ tailWord_2424458).sum := by decide
  have hdescent : baseEnd_2424458 < baseStart_2424458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424462 : List Nat := [4, 1, 1, 3, 1, 3, 3, 2, 4]
def baseStart_2424462 : Nat := 118140960795 + 2424462 * 2 ^ 59
def prefixEnd_2424462 : Nat := 4983230072969 + 3 ^ 40 * 2424462 * 2
def baseEnd_2424462 : Nat := 276647629902444114438913

theorem tailTrace_2424462 : CollatzResearch.WordTrace tailWord_2424462 prefixEnd_2424462 276647629902444114438913 := by
  unfold tailWord_2424462
  simp only [CollatzResearch.WordTrace]
  refine ⟨11053424217824464248662455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58951595828397142659533093 11053424217824464248662455)
  ·
    refine ⟨16580136326736696372993683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11053424217824464248662455 16580136326736696372993683)
    ·
      refine ⟨24870204490105044559490525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16580136326736696372993683 24870204490105044559490525)
      ·
        refine ⟨9326326683789391709808947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24870204490105044559490525 9326326683789391709808947)
        ·
          refine ⟨13989490025684087564713421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9326326683789391709808947 13989490025684087564713421)
          ·
            refine ⟨5246058759631532836767533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13989490025684087564713421 5246058759631532836767533)
            ·
              refine ⟨1967272034861824813787825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5246058759631532836767533 1967272034861824813787825)
              ·
                refine ⟨1475454026146368610340869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1967272034861824813787825 1475454026146368610340869)
                ·
                  refine ⟨276647629902444114438913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1475454026146368610340869 276647629902444114438913)
                  ·
                    rfl

theorem cell22_2424462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 2, 4].length) (baseStart_2424462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2424462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2424462 prefixEnd_2424462 := by exact prefixLift 2424462
  have htrace : WordTrace (prefixWord ++ tailWord_2424462) baseStart_2424462 baseEnd_2424462 := by
    simpa [prefixWord, tailWord_2424462, baseEnd_2424462] using wordTrace_append hprefix tailTrace_2424462
  have hstable : (prefixWord ++ tailWord_2424462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424462).length < 2 ^ (prefixWord ++ tailWord_2424462).sum := by decide
  have hdescent : baseEnd_2424462 < baseStart_2424462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424548 : List Nat := [2, 3, 1, 1, 1, 3, 1, 3, 3, 4]
def baseStart_2424548 : Nat := 118140960795 + 2424548 * 2 ^ 59
def prefixEnd_2424548 : Nat := 4983230072969 + 3 ^ 40 * 2424548 * 2
def baseEnd_2424548 : Nat := 829972329264856785666475

theorem tailTrace_2424548 : CollatzResearch.WordTrace tailWord_2424548 prefixEnd_2424548 829972329264856785666475 := by
  unfold tailWord_2424548
  simp only [CollatzResearch.WordTrace]
  refine ⟨44215265210142075338465149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58953686946856100451286865 44215265210142075338465149)
  ·
    refine ⟨16580724453803278251924431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44215265210142075338465149 16580724453803278251924431)
    ·
      refine ⟨24871086680704917377886647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16580724453803278251924431 24871086680704917377886647)
      ·
        refine ⟨37306630021057376066829971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24871086680704917377886647 37306630021057376066829971)
        ·
          refine ⟨55959945031586064100244957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37306630021057376066829971 55959945031586064100244957)
          ·
            refine ⟨20984979386844774037591859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55959945031586064100244957 20984979386844774037591859)
            ·
              refine ⟨31477469080267161056387789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20984979386844774037591859 31477469080267161056387789)
              ·
                refine ⟨11804050905100185396145421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31477469080267161056387789 11804050905100185396145421)
                ·
                  refine ⟨4426519089412569523554533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11804050905100185396145421 4426519089412569523554533)
                  ·
                    refine ⟨829972329264856785666475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4426519089412569523554533 829972329264856785666475)
                    ·
                      rfl

theorem cell22_2424548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_2424548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2424548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2424548 prefixEnd_2424548 := by exact prefixLift 2424548
  have htrace : WordTrace (prefixWord ++ tailWord_2424548) baseStart_2424548 baseEnd_2424548 := by
    simpa [prefixWord, tailWord_2424548, baseEnd_2424548] using wordTrace_append hprefix tailTrace_2424548
  have hstable : (prefixWord ++ tailWord_2424548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424548).length < 2 ^ (prefixWord ++ tailWord_2424548).sum := by decide
  have hdescent : baseEnd_2424548 < baseStart_2424548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424580 : List Nat := [2, 3, 2, 2, 1, 3, 2, 1, 6]
def baseStart_2424580 : Nat := 118140960795 + 2424580 * 2 ^ 59
def prefixEnd_2424580 : Nat := 4983230072969 + 3 ^ 40 * 2424580 * 2
def baseEnd_2424580 : Nat := 276661094506273122955459

theorem tailTrace_2424580 : CollatzResearch.WordTrace tailWord_2424580 prefixEnd_2424580 276661094506273122955459 := by
  unfold tailWord_2424580
  simp only [CollatzResearch.WordTrace]
  refine ⟨44215848778084110071047597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58954465037445480094730129 44215848778084110071047597)
  ·
    refine ⟨16580943291781541276642849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44215848778084110071047597 16580943291781541276642849)
    ·
      refine ⟨12435707468836155957482137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16580943291781541276642849 12435707468836155957482137)
      ·
        refine ⟨9326780601627116968111603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12435707468836155957482137 9326780601627116968111603)
        ·
          refine ⟨13990170902440675452167405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9326780601627116968111603 13990170902440675452167405)
          ·
            refine ⟨5246314088415253294562777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13990170902440675452167405 5246314088415253294562777)
            ·
              refine ⟨3934735566311439970922083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5246314088415253294562777 3934735566311439970922083)
              ·
                refine ⟨5902103349467159956383125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3934735566311439970922083 5902103349467159956383125)
                ·
                  refine ⟨276661094506273122955459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5902103349467159956383125 276661094506273122955459)
                  ·
                    rfl

theorem cell22_2424580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_2424580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2424580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2424580 prefixEnd_2424580 := by exact prefixLift 2424580
  have htrace : WordTrace (prefixWord ++ tailWord_2424580) baseStart_2424580 baseEnd_2424580 := by
    simpa [prefixWord, tailWord_2424580, baseEnd_2424580] using wordTrace_append hprefix tailTrace_2424580
  have hstable : (prefixWord ++ tailWord_2424580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424580).length < 2 ^ (prefixWord ++ tailWord_2424580).sum := by decide
  have hdescent : baseEnd_2424580 < baseStart_2424580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424608 : List Nat := [2, 1, 1, 5, 1, 1, 3, 8]
def baseStart_2424608 : Nat := 118140960795 + 2424608 * 2 ^ 59
def prefixEnd_2424608 : Nat := 4983230072969 + 3 ^ 40 * 2424608 * 2
def baseEnd_2424608 : Nat := 92221429832337403240699

theorem tailTrace_2424608 : CollatzResearch.WordTrace tailWord_2424608 prefixEnd_2424608 92221429832337403240699 := by
  unfold tailWord_2424608
  simp only [CollatzResearch.WordTrace]
  refine ⟨44216359400033390462057239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58955145866711187282742985 44216359400033390462057239)
  ·
    refine ⟨66324539100050085693085859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44216359400033390462057239 66324539100050085693085859)
    ·
      refine ⟨99486808650075128539628789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66324539100050085693085859 99486808650075128539628789)
      ·
        refine ⟨9326888310944543300590199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 99486808650075128539628789 9326888310944543300590199)
        ·
          refine ⟨13990332466416814950885299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9326888310944543300590199 13990332466416814950885299)
          ·
            refine ⟨20985498699625222426327949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13990332466416814950885299 20985498699625222426327949)
            ·
              refine ⟨7869562012359458409872981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20985498699625222426327949 7869562012359458409872981)
              ·
                refine ⟨92221429832337403240699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7869562012359458409872981 92221429832337403240699)
                ·
                  rfl

theorem cell22_2424608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 8].length) (baseStart_2424608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2424608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2424608 prefixEnd_2424608 := by exact prefixLift 2424608
  have htrace : WordTrace (prefixWord ++ tailWord_2424608) baseStart_2424608 baseEnd_2424608 := by
    simpa [prefixWord, tailWord_2424608, baseEnd_2424608] using wordTrace_append hprefix tailTrace_2424608
  have hstable : (prefixWord ++ tailWord_2424608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424608).length < 2 ^ (prefixWord ++ tailWord_2424608).sum := by decide
  have hdescent : baseEnd_2424608 < baseStart_2424608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424610 : List Nat := [3, 3, 1, 1, 2, 1, 2, 3, 2, 4]
def baseStart_2424610 : Nat := 118140960795 + 2424610 * 2 ^ 59
def prefixEnd_2424610 : Nat := 4983230072969 + 3 ^ 40 * 2424610 * 2
def baseEnd_2424610 : Nat := 829993553131909290616285

theorem tailTrace_2424610 : CollatzResearch.WordTrace tailWord_2424610 prefixEnd_2424610 829993553131909290616285 := by
  unfold tailWord_2424610
  simp only [CollatzResearch.WordTrace]
  refine ⟨22108197936514883816421821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58955194497373023510458189 22108197936514883816421821)
  ·
    refine ⟨8290574226193081431158183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22108197936514883816421821 8290574226193081431158183)
    ·
      refine ⟨12435861339289622146737275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8290574226193081431158183 12435861339289622146737275)
      ·
        refine ⟨18653792008934433220105913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12435861339289622146737275 18653792008934433220105913)
        ·
          refine ⟨13990344006700824915079435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18653792008934433220105913 13990344006700824915079435)
          ·
            refine ⟨20985516010051237372619153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13990344006700824915079435 20985516010051237372619153)
            ·
              refine ⟨15739137007538428029464365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20985516010051237372619153 15739137007538428029464365)
              ·
                refine ⟨5902176377826910511049137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15739137007538428029464365 5902176377826910511049137)
                ·
                  refine ⟨4426632283370182883286853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5902176377826910511049137 4426632283370182883286853)
                  ·
                    refine ⟨829993553131909290616285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4426632283370182883286853 829993553131909290616285)
                    ·
                      rfl

theorem cell22_2424610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_2424610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2424610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2424610 prefixEnd_2424610 := by exact prefixLift 2424610
  have htrace : WordTrace (prefixWord ++ tailWord_2424610) baseStart_2424610 baseEnd_2424610 := by
    simpa [prefixWord, tailWord_2424610, baseEnd_2424610] using wordTrace_append hprefix tailTrace_2424610
  have hstable : (prefixWord ++ tailWord_2424610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424610).length < 2 ^ (prefixWord ++ tailWord_2424610).sum := by decide
  have hdescent : baseEnd_2424610 < baseStart_2424610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424646 : List Nat := [6, 1, 1, 2, 1, 2, 1, 3, 2, 3]
def baseStart_2424646 : Nat := 118140960795 + 2424646 * 2 ^ 59
def prefixEnd_2424646 : Nat := 4983230072969 + 3 ^ 40 * 2424646 * 2
def baseEnd_2424646 : Nat := 830005876667617196716175

theorem tailTrace_2424646 : CollatzResearch.WordTrace tailWord_2424646 prefixEnd_2424646 830005876667617196716175 := by
  unfold tailWord_2424646
  simp only [CollatzResearch.WordTrace]
  refine ⟨2763565774185284794187431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 58956069849286075609331861 2763565774185284794187431)
  ·
    refine ⟨4145348661277927191281147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2763565774185284794187431 4145348661277927191281147)
    ·
      refine ⟨6218022991916890786921721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4145348661277927191281147 6218022991916890786921721)
      ·
        refine ⟨4663517243937668090191291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6218022991916890786921721 4663517243937668090191291)
        ·
          refine ⟨6995275865906502135286937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4663517243937668090191291 6995275865906502135286937)
          ·
            refine ⟨5246456899429876601465203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6995275865906502135286937 5246456899429876601465203)
            ·
              refine ⟨7869685349144814902197805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5246456899429876601465203 7869685349144814902197805)
              ·
                refine ⟨2951132005929305588324177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7869685349144814902197805 2951132005929305588324177)
                ·
                  refine ⟨2213349004446979191243133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2951132005929305588324177 2213349004446979191243133)
                  ·
                    refine ⟨830005876667617196716175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2213349004446979191243133 830005876667617196716175)
                    ·
                      rfl

theorem cell22_2424646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_2424646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2424646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2424646 prefixEnd_2424646 := by exact prefixLift 2424646
  have htrace : WordTrace (prefixWord ++ tailWord_2424646) baseStart_2424646 baseEnd_2424646 := by
    simpa [prefixWord, tailWord_2424646, baseEnd_2424646] using wordTrace_append hprefix tailTrace_2424646
  have hstable : (prefixWord ++ tailWord_2424646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424646).length < 2 ^ (prefixWord ++ tailWord_2424646).sum := by decide
  have hdescent : baseEnd_2424646 < baseStart_2424646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424702 : List Nat := [4, 2, 3, 1, 1, 1, 1, 1, 1, 7]
def baseStart_2424702 : Nat := 118140960795 + 2424702 * 2 ^ 59
def prefixEnd_2424702 : Nat := 4983230072969 + 3 ^ 40 * 2424702 * 2
def baseEnd_2424702 : Nat := 830025046612051717316003

theorem tailTrace_2424702 : CollatzResearch.WordTrace tailWord_2424702 prefixEnd_2424702 830025046612051717316003 := by
  unfold tailWord_2424702
  simp only [CollatzResearch.WordTrace]
  refine ⟨11054518407715779372254545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58957431507817489985357573 11054518407715779372254545)
  ·
    refine ⟨8290888805786834529190909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11054518407715779372254545 8290888805786834529190909)
    ·
      refine ⟨3109083302170062948446591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8290888805786834529190909 3109083302170062948446591)
      ·
        refine ⟨4663624953255094422669887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3109083302170062948446591 4663624953255094422669887)
        ·
          refine ⟨6995437429882641634004831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4663624953255094422669887 6995437429882641634004831)
          ·
            refine ⟨10493156144823962451007247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6995437429882641634004831 10493156144823962451007247)
            ·
              refine ⟨15739734217235943676510871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10493156144823962451007247 15739734217235943676510871)
              ·
                refine ⟨23609601325853915514766307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15739734217235943676510871 23609601325853915514766307)
                ·
                  refine ⟨35414401988780873272149461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23609601325853915514766307 35414401988780873272149461)
                  ·
                    refine ⟨830025046612051717316003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35414401988780873272149461 830025046612051717316003)
                    ·
                      rfl

theorem cell22_2424702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_2424702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2424702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2424702 prefixEnd_2424702 := by exact prefixLift 2424702
  have htrace : WordTrace (prefixWord ++ tailWord_2424702) baseStart_2424702 baseEnd_2424702 := by
    simpa [prefixWord, tailWord_2424702, baseEnd_2424702] using wordTrace_append hprefix tailTrace_2424702
  have hstable : (prefixWord ++ tailWord_2424702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424702).length < 2 ^ (prefixWord ++ tailWord_2424702).sum := by decide
  have hdescent : baseEnd_2424702 < baseStart_2424702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424882 : List Nat := [3, 2, 1, 1, 2, 3, 1, 3, 1, 5]
def baseStart_2424882 : Nat := 118140960795 + 2424882 * 2 ^ 59
def prefixEnd_2424882 : Nat := 4983230072969 + 3 ^ 40 * 2424882 * 2
def baseEnd_2424882 : Nat := 830086664290591247815451

theorem tailTrace_2424882 : CollatzResearch.WordTrace tailWord_2424882 prefixEnd_2424882 830086664290591247815451 := by
  unfold tailWord_2424882
  simp only [CollatzResearch.WordTrace]
  refine ⟨22110678100268531429897225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58961808267382750479725933 22110678100268531429897225)
  ·
    refine ⟨16583008575201398572422919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22110678100268531429897225 16583008575201398572422919)
    ·
      refine ⟨24874512862802097858634379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16583008575201398572422919 24874512862802097858634379)
      ·
        refine ⟨37311769294203146787951569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24874512862802097858634379 37311769294203146787951569)
        ·
          refine ⟨27983826970652360090963677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37311769294203146787951569 27983826970652360090963677)
          ·
            refine ⟨10493935113994635034111379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27983826970652360090963677 10493935113994635034111379)
            ·
              refine ⟨15740902670991952551167069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10493935113994635034111379 15740902670991952551167069)
              ·
                refine ⟨5902838501621982206687651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15740902670991952551167069 5902838501621982206687651)
                ·
                  refine ⟨8854257752432973310031477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5902838501621982206687651 8854257752432973310031477)
                  ·
                    refine ⟨830086664290591247815451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8854257752432973310031477 830086664290591247815451)
                    ·
                      rfl

theorem cell22_2424882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_2424882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2424882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2424882 prefixEnd_2424882 := by exact prefixLift 2424882
  have htrace : WordTrace (prefixWord ++ tailWord_2424882) baseStart_2424882 baseEnd_2424882 := by
    simpa [prefixWord, tailWord_2424882, baseEnd_2424882] using wordTrace_append hprefix tailTrace_2424882
  have hstable : (prefixWord ++ tailWord_2424882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424882).length < 2 ^ (prefixWord ++ tailWord_2424882).sum := by decide
  have hdescent : baseEnd_2424882 < baseStart_2424882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424895 : List Nat := [1, 1, 2, 2, 3, 1, 2, 10]
def baseStart_2424895 : Nat := 118140960795 + 2424895 * 2 ^ 59
def prefixEnd_2424895 : Nat := 4983230072969 + 3 ^ 40 * 2424895 * 2
def baseEnd_2424895 : Nat := 92232346050695949693379

theorem tailTrace_2424895 : CollatzResearch.WordTrace tailWord_2424895 prefixEnd_2424895 92232346050695949693379 := by
  unfold tailWord_2424895
  simp only [CollatzResearch.WordTrace]
  refine ⟨88443186550027028939812139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58962124366684685959874759 88443186550027028939812139)
  ·
    refine ⟨132664779825040543409718209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88443186550027028939812139 132664779825040543409718209)
    ·
      refine ⟨99498584868780407557288657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132664779825040543409718209 99498584868780407557288657)
      ·
        refine ⟨74623938651585305667966493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99498584868780407557288657 74623938651585305667966493)
        ·
          refine ⟨27983976994344489625487435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74623938651585305667966493 27983976994344489625487435)
          ·
            refine ⟨41975965491516734438231153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27983976994344489625487435 41975965491516734438231153)
            ·
              refine ⟨31481974118637550828673365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41975965491516734438231153 31481974118637550828673365)
              ·
                refine ⟨92232346050695949693379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 31481974118637550828673365 92232346050695949693379)
                ·
                  rfl

theorem cell22_2424895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 10].length) (baseStart_2424895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2424895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2424895 prefixEnd_2424895 := by exact prefixLift 2424895
  have htrace : WordTrace (prefixWord ++ tailWord_2424895) baseStart_2424895 baseEnd_2424895 := by
    simpa [prefixWord, tailWord_2424895, baseEnd_2424895] using wordTrace_append hprefix tailTrace_2424895
  have hstable : (prefixWord ++ tailWord_2424895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424895).length < 2 ^ (prefixWord ++ tailWord_2424895).sum := by decide
  have hdescent : baseEnd_2424895 < baseStart_2424895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424918 : List Nat := [5, 2, 2, 1, 1, 1, 2, 4, 4]
def baseStart_2424918 : Nat := 118140960795 + 2424918 * 2 ^ 59
def prefixEnd_2424918 : Nat := 4983230072969 + 3 ^ 40 * 2424918 * 2
def baseEnd_2424918 : Nat := 276699662608766384638447

theorem tailTrace_2424918 : CollatzResearch.WordTrace tailWord_2424918 prefixEnd_2424918 276699662608766384638447 := by
  unfold tailWord_2424918
  simp only [CollatzResearch.WordTrace]
  refine ⟨5527751589308981491743713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58962683619295802578599605 5527751589308981491743713)
  ·
    refine ⟨4145813691981736118807785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5527751589308981491743713 4145813691981736118807785)
    ·
      refine ⟨3109360268986302089105839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4145813691981736118807785 3109360268986302089105839)
      ·
        refine ⟨4664040403479453133658759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3109360268986302089105839 4664040403479453133658759)
        ·
          refine ⟨6996060605219179700488139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4664040403479453133658759 6996060605219179700488139)
          ·
            refine ⟨10494090907828769550732209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6996060605219179700488139 10494090907828769550732209)
            ·
              refine ⟨7870568180871577163049157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10494090907828769550732209 7870568180871577163049157)
              ·
                refine ⟨1475731533913420718071717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7870568180871577163049157 1475731533913420718071717)
                ·
                  refine ⟨276699662608766384638447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1475731533913420718071717 276699662608766384638447)
                  ·
                    rfl

theorem cell22_2424918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_2424918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2424918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2424918 prefixEnd_2424918 := by exact prefixLift 2424918
  have htrace : WordTrace (prefixWord ++ tailWord_2424918) baseStart_2424918 baseEnd_2424918 := by
    simpa [prefixWord, tailWord_2424918, baseEnd_2424918] using wordTrace_append hprefix tailTrace_2424918
  have hstable : (prefixWord ++ tailWord_2424918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424918).length < 2 ^ (prefixWord ++ tailWord_2424918).sum := by decide
  have hdescent : baseEnd_2424918 < baseStart_2424918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424944 : List Nat := [2, 1, 1, 1, 5, 2, 2, 2, 3, 3]
def baseStart_2424944 : Nat := 118140960795 + 2424944 * 2 ^ 59
def prefixEnd_2424944 : Nat := 4983230072969 + 3 ^ 40 * 2424944 * 2
def baseEnd_2424944 : Nat := 830107888157643752765261

theorem tailTrace_2424944 : CollatzResearch.WordTrace tailWord_2424944 prefixEnd_2424944 830107888157643752765261 := by
  unfold tailWord_2424944
  simp only [CollatzResearch.WordTrace]
  refine ⟨44222486863424755154172943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58963315817899673538897257 44222486863424755154172943)
  ·
    refine ⟨66333730295137132731259415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44222486863424755154172943 66333730295137132731259415)
    ·
      refine ⟨99500595442705699096889123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66333730295137132731259415 99500595442705699096889123)
      ·
        refine ⟨149250893164058548645333685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99500595442705699096889123 149250893164058548645333685)
        ·
          refine ⟨13992271234130488935500033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 149250893164058548645333685 13992271234130488935500033)
          ·
            refine ⟨10494203425597866701625025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13992271234130488935500033 10494203425597866701625025)
            ·
              refine ⟨7870652569198400026218769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10494203425597866701625025 7870652569198400026218769)
              ·
                refine ⟨5902989426898800019664077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7870652569198400026218769 5902989426898800019664077)
                ·
                  refine ⟨2213621035087050007374029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5902989426898800019664077 2213621035087050007374029)
                  ·
                    refine ⟨830107888157643752765261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2213621035087050007374029 830107888157643752765261)
                    ·
                      rfl

theorem cell22_2424944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 3, 3].length) (baseStart_2424944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2424944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2424944 prefixEnd_2424944 := by exact prefixLift 2424944
  have htrace : WordTrace (prefixWord ++ tailWord_2424944) baseStart_2424944 baseEnd_2424944 := by
    simpa [prefixWord, tailWord_2424944, baseEnd_2424944] using wordTrace_append hprefix tailTrace_2424944
  have hstable : (prefixWord ++ tailWord_2424944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424944).length < 2 ^ (prefixWord ++ tailWord_2424944).sum := by decide
  have hdescent : baseEnd_2424944 < baseStart_2424944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2424957 : List Nat := [1, 4, 1, 1, 3, 2, 1, 2, 7]
def baseStart_2424957 : Nat := 118140960795 + 2424957 * 2 ^ 59
def prefixEnd_2424957 : Nat := 4983230072969 + 3 ^ 40 * 2424957 * 2
def baseEnd_2424957 : Nat := 276704112774438684063407

theorem tailTrace_2424957 : CollatzResearch.WordTrace tailWord_2424957 prefixEnd_2424957 276704112774438684063407 := by
  unfold tailWord_2424957
  simp only [CollatzResearch.WordTrace]
  refine ⟨88445447875802413528569125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58963631917201609019046083 88445447875802413528569125)
  ·
    refine ⟨16583521476712952536606711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88445447875802413528569125 16583521476712952536606711)
    ·
      refine ⟨24875282215069428804910067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16583521476712952536606711 24875282215069428804910067)
      ·
        refine ⟨37312923322604143207365101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24875282215069428804910067 37312923322604143207365101)
        ·
          refine ⟨13992346245976553702761913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37312923322604143207365101 13992346245976553702761913)
          ·
            refine ⟨10494259684482415277071435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13992346245976553702761913 10494259684482415277071435)
            ·
              refine ⟨15741389526723622915607153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10494259684482415277071435 15741389526723622915607153)
              ·
                refine ⟨11806042145042717186705365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15741389526723622915607153 11806042145042717186705365)
                ·
                  refine ⟨276704112774438684063407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11806042145042717186705365 276704112774438684063407)
                  ·
                    rfl

theorem cell22_2424957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_2424957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2424957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2424957 prefixEnd_2424957 := by exact prefixLift 2424957
  have htrace : WordTrace (prefixWord ++ tailWord_2424957) baseStart_2424957 baseEnd_2424957 := by
    simpa [prefixWord, tailWord_2424957, baseEnd_2424957] using wordTrace_append hprefix tailTrace_2424957
  have hstable : (prefixWord ++ tailWord_2424957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2424957).length < 2 ^ (prefixWord ++ tailWord_2424957).sum := by decide
  have hdescent : baseEnd_2424957 < baseStart_2424957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2424957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
