import V185TrunkScan21Chunk079

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_969393 : List Nat := [1, 2, 2, 6, 2, 1, 2, 1, 4]
def baseStart_969393 : Nat := 118140960795 + 969393 * 2 ^ 59
def prefixEnd_969393 : Nat := 4983230072969 + 3 ^ 40 * 969393 * 2
def baseEnd_969393 : Nat := 221228689824013768501933

theorem tailTrace_969393 : CollatzResearch.WordTrace tailWord_969393 prefixEnd_969393 221228689824013768501933 := by
  unfold tailWord_969393
  simp only [CollatzResearch.WordTrace]
  refine ⟨35356667377062194988672833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23571111584708129992448555 35356667377062194988672833)
  ·
    refine ⟨26517500532796646241504625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35356667377062194988672833 26517500532796646241504625)
    ·
      refine ⟨19888125399597484681128469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26517500532796646241504625 19888125399597484681128469)
      ·
        refine ⟨932255878106132094427897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19888125399597484681128469 932255878106132094427897)
        ·
          refine ⟨699191908579599070820923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 932255878106132094427897 699191908579599070820923)
          ·
            refine ⟨1048787862869398606231385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699191908579599070820923 1048787862869398606231385)
            ·
              refine ⟨786590897152048954673539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1048787862869398606231385 786590897152048954673539)
              ·
                refine ⟨1179886345728073432010309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 786590897152048954673539 1179886345728073432010309)
                ·
                  refine ⟨221228689824013768501933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1179886345728073432010309 221228689824013768501933)
                  ·
                    rfl

theorem cell21_969393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 1, 4].length) (baseStart_969393 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_969393 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_969393 prefixEnd_969393 := by exact prefixLift 969393
  have htrace : WordTrace (prefixWord ++ tailWord_969393) baseStart_969393 baseEnd_969393 := by
    simpa [prefixWord, tailWord_969393, baseEnd_969393] using wordTrace_append hprefix tailTrace_969393
  have hstable : (prefixWord ++ tailWord_969393).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969393).length < 2 ^ (prefixWord ++ tailWord_969393).sum := by decide
  have hdescent : baseEnd_969393 < baseStart_969393 := by decide
  rcases family_descends (prefixWord ++ tailWord_969393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969480 : List Nat := [2, 1, 3, 2, 2, 3, 2, 3, 3]
def baseStart_969480 : Nat := 118140960795 + 969480 * 2 ^ 59
def prefixEnd_969480 : Nat := 4983230072969 + 3 ^ 40 * 969480 * 2
def baseEnd_969480 : Nat := 221248544409320950551755

theorem tailTrace_969480 : CollatzResearch.WordTrace tailWord_969480 prefixEnd_969480 221248544409320950551755 := by
  unfold tailWord_969480
  simp only [CollatzResearch.WordTrace]
  refine ⟨17679920263873504423544947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23573227018498005898059929 17679920263873504423544947)
  ·
    refine ⟨26519880395810256635317421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17679920263873504423544947 26519880395810256635317421)
    ·
      refine ⟨9944955148428846238244033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26519880395810256635317421 9944955148428846238244033)
      ·
        refine ⟨7458716361321634678683025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9944955148428846238244033 7458716361321634678683025)
        ·
          refine ⟨5594037270991226009012269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7458716361321634678683025 5594037270991226009012269)
          ·
            refine ⟨2097763976621709753379601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5594037270991226009012269 2097763976621709753379601)
            ·
              refine ⟨1573322982466282315034701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2097763976621709753379601 1573322982466282315034701)
              ·
                refine ⟨589996118424855868138013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1573322982466282315034701 589996118424855868138013)
                ·
                  refine ⟨221248544409320950551755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 589996118424855868138013 221248544409320950551755)
                  ·
                    rfl

theorem cell21_969480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 3, 3].length) (baseStart_969480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_969480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_969480 prefixEnd_969480 := by exact prefixLift 969480
  have htrace : WordTrace (prefixWord ++ tailWord_969480) baseStart_969480 baseEnd_969480 := by
    simpa [prefixWord, tailWord_969480, baseEnd_969480] using wordTrace_append hprefix tailTrace_969480
  have hstable : (prefixWord ++ tailWord_969480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969480).length < 2 ^ (prefixWord ++ tailWord_969480).sum := by decide
  have hdescent : baseEnd_969480 < baseStart_969480 := by decide
  rcases family_descends (prefixWord ++ tailWord_969480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969522 : List Nat := [3, 2, 1, 1, 3, 1, 1, 4, 5]
def baseStart_969522 : Nat := 118140960795 + 969522 * 2 ^ 59
def prefixEnd_969522 : Nat := 4983230072969 + 3 ^ 40 * 969522 * 2
def baseEnd_969522 : Nat := 221258129381538210851669

theorem tailTrace_969522 : CollatzResearch.WordTrace tailWord_969522 prefixEnd_969522 221258129381538210851669 := by
  unfold tailWord_969522
  simp only [CollatzResearch.WordTrace]
  refine ⟨8840343098398712505029705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23574248262396566680079213 8840343098398712505029705)
  ·
    refine ⟨6630257323799034378772279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8840343098398712505029705 6630257323799034378772279)
    ·
      refine ⟨9945385985698551568158419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6630257323799034378772279 9945385985698551568158419)
      ·
        refine ⟨14918078978547827352237629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9945385985698551568158419 14918078978547827352237629)
        ·
          refine ⟨5594279616955435257089111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14918078978547827352237629 5594279616955435257089111)
          ·
            refine ⟨8391419425433152885633667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5594279616955435257089111 8391419425433152885633667)
            ·
              refine ⟨12587129138149729328450501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8391419425433152885633667 12587129138149729328450501)
              ·
                refine ⟨2360086713403074249084469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12587129138149729328450501 2360086713403074249084469)
                ·
                  refine ⟨221258129381538210851669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2360086713403074249084469 221258129381538210851669)
                  ·
                    rfl

theorem cell21_969522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_969522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_969522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_969522 prefixEnd_969522 := by exact prefixLift 969522
  have htrace : WordTrace (prefixWord ++ tailWord_969522) baseStart_969522 baseEnd_969522 := by
    simpa [prefixWord, tailWord_969522, baseEnd_969522] using wordTrace_append hprefix tailTrace_969522
  have hstable : (prefixWord ++ tailWord_969522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969522).length < 2 ^ (prefixWord ++ tailWord_969522).sum := by decide
  have hdescent : baseEnd_969522 < baseStart_969522 := by decide
  rcases family_descends (prefixWord ++ tailWord_969522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969525 : List Nat := [1, 3, 3, 1, 3, 3, 2, 5]
def baseStart_969525 : Nat := 118140960795 + 969525 * 2 ^ 59
def prefixEnd_969525 : Nat := 4983230072969 + 3 ^ 40 * 969525 * 2
def baseEnd_969525 : Nat := 73752938007470290767221

theorem tailTrace_969525 : CollatzResearch.WordTrace tailWord_969525 prefixEnd_969525 73752938007470290767221 := by
  unfold tailWord_969525
  simp only [CollatzResearch.WordTrace]
  refine ⟨35361481812583981532478029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23574321208389321021652019 35361481812583981532478029)
  ·
    refine ⟨13260555679718993074679261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35361481812583981532478029 13260555679718993074679261)
    ·
      refine ⟨4972708379894622403004723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13260555679718993074679261 4972708379894622403004723)
      ·
        refine ⟨7459062569841933604507085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4972708379894622403004723 7459062569841933604507085)
        ·
          refine ⟨2797148463690725101690157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7459062569841933604507085 2797148463690725101690157)
          ·
            refine ⟨1048930673884021913133809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2797148463690725101690157 1048930673884021913133809)
            ·
              refine ⟨786698005413016434850357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1048930673884021913133809 786698005413016434850357)
              ·
                refine ⟨73752938007470290767221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 786698005413016434850357 73752938007470290767221)
                ·
                  rfl

theorem cell21_969525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 5].length) (baseStart_969525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_969525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_969525 prefixEnd_969525 := by exact prefixLift 969525
  have htrace : WordTrace (prefixWord ++ tailWord_969525) baseStart_969525 baseEnd_969525 := by
    simpa [prefixWord, tailWord_969525, baseEnd_969525] using wordTrace_append hprefix tailTrace_969525
  have hstable : (prefixWord ++ tailWord_969525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969525).length < 2 ^ (prefixWord ++ tailWord_969525).sum := by decide
  have hdescent : baseEnd_969525 < baseStart_969525 := by decide
  rcases family_descends (prefixWord ++ tailWord_969525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969542 : List Nat := [6, 1, 1, 2, 2, 2, 7]
def baseStart_969542 : Nat := 118140960795 + 969542 * 2 ^ 59
def prefixEnd_969542 : Nat := 4983230072969 + 3 ^ 40 * 969542 * 2
def baseEnd_969542 : Nat := 24584743739335846724255

theorem tailTrace_969542 : CollatzResearch.WordTrace tailWord_969542 prefixEnd_969542 24584743739335846724255 := by
  unfold tailWord_969542
  simp only [CollatzResearch.WordTrace]
  refine ⟨1105065682922574794870215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23574734569014928957231253 1105065682922574794870215)
  ·
    refine ⟨1657598524383862192305323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1105065682922574794870215 1657598524383862192305323)
    ·
      refine ⟨2486397786575793288457985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1657598524383862192305323 2486397786575793288457985)
      ·
        refine ⟨1864798339931844966343489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2486397786575793288457985 1864798339931844966343489)
        ·
          refine ⟨1398598754948883724757617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1864798339931844966343489 1398598754948883724757617)
          ·
            refine ⟨1048949066211662793568213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1398598754948883724757617 1048949066211662793568213)
            ·
              refine ⟨24584743739335846724255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1048949066211662793568213 24584743739335846724255)
              ·
                rfl

theorem cell21_969542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 7].length) (baseStart_969542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_969542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_969542 prefixEnd_969542 := by exact prefixLift 969542
  have htrace : WordTrace (prefixWord ++ tailWord_969542) baseStart_969542 baseEnd_969542 := by
    simpa [prefixWord, tailWord_969542, baseEnd_969542] using wordTrace_append hprefix tailTrace_969542
  have hstable : (prefixWord ++ tailWord_969542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969542).length < 2 ^ (prefixWord ++ tailWord_969542).sum := by decide
  have hdescent : baseEnd_969542 < baseStart_969542 := by decide
  rcases family_descends (prefixWord ++ tailWord_969542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969556 : List Nat := [2, 4, 1, 1, 4, 2, 1, 1, 5]
def baseStart_969556 : Nat := 118140960795 + 969556 * 2 ^ 59
def prefixEnd_969556 : Nat := 4983230072969 + 3 ^ 40 * 969556 * 2
def baseEnd_969556 : Nat := 221265888644761707284933

theorem tailTrace_969556 : CollatzResearch.WordTrace tailWord_969556 prefixEnd_969556 221265888644761707284933 := by
  unfold tailWord_969556
  simp only [CollatzResearch.WordTrace]
  refine ⟨17681306237735836913428261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23575074983647782551237681 17681306237735836913428261)
  ·
    refine ⟨3315244919575469421267799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17681306237735836913428261 3315244919575469421267799)
    ·
      refine ⟨4972867379363204131901699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3315244919575469421267799 4972867379363204131901699)
      ·
        refine ⟨7459301069044806197852549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4972867379363204131901699 7459301069044806197852549)
        ·
          refine ⟨1398618950445901162097353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7459301069044806197852549 1398618950445901162097353)
          ·
            refine ⟨1048964212834425871573015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1398618950445901162097353 1048964212834425871573015)
            ·
              refine ⟨1573446319251638807359523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1048964212834425871573015 1573446319251638807359523)
              ·
                refine ⟨2360169478877458211039285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1573446319251638807359523 2360169478877458211039285)
                ·
                  refine ⟨221265888644761707284933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2360169478877458211039285 221265888644761707284933)
                  ·
                    rfl

theorem cell21_969556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_969556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_969556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_969556 prefixEnd_969556 := by exact prefixLift 969556
  have htrace : WordTrace (prefixWord ++ tailWord_969556) baseStart_969556 baseEnd_969556 := by
    simpa [prefixWord, tailWord_969556, baseEnd_969556] using wordTrace_append hprefix tailTrace_969556
  have hstable : (prefixWord ++ tailWord_969556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969556).length < 2 ^ (prefixWord ++ tailWord_969556).sum := by decide
  have hdescent : baseEnd_969556 < baseStart_969556 := by decide
  rcases family_descends (prefixWord ++ tailWord_969556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969567 : List Nat := [1, 1, 2, 3, 1, 3, 4, 6]
def baseStart_969567 : Nat := 118140960795 + 969567 * 2 ^ 59
def prefixEnd_969567 : Nat := 4983230072969 + 3 ^ 40 * 969567 * 2
def baseEnd_969567 : Nat := 73756132998209377533859

theorem tailTrace_969567 : CollatzResearch.WordTrace tailWord_969567 prefixEnd_969567 73756132998209377533859 := by
  unfold tailWord_969567
  simp only [CollatzResearch.WordTrace]
  refine ⟨35363013678431822705506955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23575342452287881803671303 35363013678431822705506955)
  ·
    refine ⟨53044520517647734058260433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35363013678431822705506955 53044520517647734058260433)
    ·
      refine ⟨39783390388235800543695325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53044520517647734058260433 39783390388235800543695325)
      ·
        refine ⟨14918771395588425203885747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39783390388235800543695325 14918771395588425203885747)
        ·
          refine ⟨22378157093382637805828621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14918771395588425203885747 22378157093382637805828621)
          ·
            refine ⟨8391808910018489177185733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22378157093382637805828621 8391808910018489177185733)
            ·
              refine ⟨1573464170628466720722325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8391808910018489177185733 1573464170628466720722325)
              ·
                refine ⟨73756132998209377533859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1573464170628466720722325 73756132998209377533859)
                ·
                  rfl

theorem cell21_969567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 6].length) (baseStart_969567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_969567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_969567 prefixEnd_969567 := by exact prefixLift 969567
  have htrace : WordTrace (prefixWord ++ tailWord_969567) baseStart_969567 baseEnd_969567 := by
    simpa [prefixWord, tailWord_969567, baseEnd_969567] using wordTrace_append hprefix tailTrace_969567
  have hstable : (prefixWord ++ tailWord_969567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969567).length < 2 ^ (prefixWord ++ tailWord_969567).sum := by decide
  have hdescent : baseEnd_969567 < baseStart_969567 := by decide
  rcases family_descends (prefixWord ++ tailWord_969567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969612 : List Nat := [2, 2, 1, 2, 1, 2, 2, 3, 6]
def baseStart_969612 : Nat := 118140960795 + 969612 * 2 ^ 59
def prefixEnd_969612 : Nat := 4983230072969 + 3 ^ 40 * 969612 * 2
def baseEnd_969612 : Nat := 221278668607718054351485

theorem tailTrace_969612 : CollatzResearch.WordTrace tailWord_969612 prefixEnd_969612 221278668607718054351485 := by
  unfold tailWord_969612
  simp only [CollatzResearch.WordTrace]
  refine ⟨17682327481634397695447545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23576436642179196927263393 17682327481634397695447545)
  ·
    refine ⟨13261745611225798271585659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17682327481634397695447545 13261745611225798271585659)
    ·
      refine ⟨19892618416838697407378489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13261745611225798271585659 19892618416838697407378489)
      ·
        refine ⟨14919463812629023055533867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19892618416838697407378489 14919463812629023055533867)
        ·
          refine ⟨22379195718943534583300801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14919463812629023055533867 22379195718943534583300801)
          ·
            refine ⟨16784396789207650937475601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22379195718943534583300801 16784396789207650937475601)
            ·
              refine ⟨12588297591905738203106701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16784396789207650937475601 12588297591905738203106701)
              ·
                refine ⟨4720611596964651826165013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12588297591905738203106701 4720611596964651826165013)
                ·
                  refine ⟨221278668607718054351485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4720611596964651826165013 221278668607718054351485)
                  ·
                    rfl

theorem cell21_969612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_969612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_969612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_969612 prefixEnd_969612 := by exact prefixLift 969612
  have htrace : WordTrace (prefixWord ++ tailWord_969612) baseStart_969612 baseEnd_969612 := by
    simpa [prefixWord, tailWord_969612, baseEnd_969612] using wordTrace_append hprefix tailTrace_969612
  have hstable : (prefixWord ++ tailWord_969612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969612).length < 2 ^ (prefixWord ++ tailWord_969612).sum := by decide
  have hdescent : baseEnd_969612 < baseStart_969612 := by decide
  rcases family_descends (prefixWord ++ tailWord_969612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969618 : List Nat := [3, 2, 3, 2, 3, 1, 1, 6]
def baseStart_969618 : Nat := 118140960795 + 969618 * 2 ^ 59
def prefixEnd_969618 : Nat := 4983230072969 + 3 ^ 40 * 969618 * 2
def baseEnd_969618 : Nat := 73760012629821125750491

theorem tailTrace_969618 : CollatzResearch.WordTrace tailWord_969618 prefixEnd_969618 73760012629821125750491 := by
  unfold tailWord_969618
  simp only [CollatzResearch.WordTrace]
  refine ⟨8841218450311764603903377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23576582534164705610409005 8841218450311764603903377)
  ·
    refine ⟨6630913837733823452927533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8841218450311764603903377 6630913837733823452927533)
    ·
      refine ⟨2486592689150183794847825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6630913837733823452927533 2486592689150183794847825)
      ·
        refine ⟨1864944516862637846135869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2486592689150183794847825 1864944516862637846135869)
        ·
          refine ⟨699354193823489192300951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1864944516862637846135869 699354193823489192300951)
          ·
            refine ⟨1049031290735233788451427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699354193823489192300951 1049031290735233788451427)
            ·
              refine ⟨1573546936102850682677141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1049031290735233788451427 1573546936102850682677141)
              ·
                refine ⟨73760012629821125750491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1573546936102850682677141 73760012629821125750491)
                ·
                  rfl

theorem cell21_969618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 6].length) (baseStart_969618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_969618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_969618 prefixEnd_969618 := by exact prefixLift 969618
  have htrace : WordTrace (prefixWord ++ tailWord_969618) baseStart_969618 baseEnd_969618 := by
    simpa [prefixWord, tailWord_969618, baseEnd_969618] using wordTrace_append hprefix tailTrace_969618
  have hstable : (prefixWord ++ tailWord_969618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969618).length < 2 ^ (prefixWord ++ tailWord_969618).sum := by decide
  have hdescent : baseEnd_969618 < baseStart_969618 := by decide
  rcases family_descends (prefixWord ++ tailWord_969618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969629 : List Nat := [1, 4, 2, 1, 2, 1, 1, 5, 4]
def baseStart_969629 : Nat := 118140960795 + 969629 * 2 ^ 59
def prefixEnd_969629 : Nat := 4983230072969 + 3 ^ 40 * 969629 * 2
def baseEnd_969629 : Nat := 221282548239329802568117

theorem tailTrace_969629 : CollatzResearch.WordTrace tailWord_969629 prefixEnd_969629 221282548239329802568117 := by
  unfold tailWord_969629
  simp only [CollatzResearch.WordTrace]
  refine ⟨35365275004207207294263941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23576850002804804862842627 35365275004207207294263941)
  ·
    refine ⟨6630989063288851367674489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35365275004207207294263941 6630989063288851367674489)
    ·
      refine ⟨4973241797466638525755867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6630989063288851367674489 4973241797466638525755867)
      ·
        refine ⟨7459862696199957788633801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4973241797466638525755867 7459862696199957788633801)
        ·
          refine ⟨5594897022149968341475351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7459862696199957788633801 5594897022149968341475351)
          ·
            refine ⟨8392345533224952512213027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5594897022149968341475351 8392345533224952512213027)
            ·
              refine ⟨12588518299837428768319541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8392345533224952512213027 12588518299837428768319541)
              ·
                refine ⟨1180173590609758947029957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12588518299837428768319541 1180173590609758947029957)
                ·
                  refine ⟨221282548239329802568117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1180173590609758947029957 221282548239329802568117)
                  ·
                    rfl

theorem cell21_969629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_969629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_969629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_969629 prefixEnd_969629 := by exact prefixLift 969629
  have htrace : WordTrace (prefixWord ++ tailWord_969629) baseStart_969629 baseEnd_969629 := by
    simpa [prefixWord, tailWord_969629, baseEnd_969629] using wordTrace_append hprefix tailTrace_969629
  have hstable : (prefixWord ++ tailWord_969629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969629).length < 2 ^ (prefixWord ++ tailWord_969629).sum := by decide
  have hdescent : baseEnd_969629 < baseStart_969629 := by decide
  rcases family_descends (prefixWord ++ tailWord_969629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969784 : List Nat := [2, 1, 2, 1, 5, 1, 4, 2, 3]
def baseStart_969784 : Nat := 118140960795 + 969784 * 2 ^ 59
def prefixEnd_969784 : Nat := 4983230072969 + 3 ^ 40 * 969784 * 2
def baseEnd_969784 : Nat := 221317921351083977484467

theorem tailTrace_969784 : CollatzResearch.WordTrace tailWord_969784 prefixEnd_969784 221317921351083977484467 := by
  unfold tailWord_969784
  simp only [CollatzResearch.WordTrace]
  refine ⟨17685464159322834383078203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23580618879097112510770937 17685464159322834383078203)
  ·
    refine ⟨26528196238984251574617305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17685464159322834383078203 26528196238984251574617305)
    ·
      refine ⟨19896147179238188680962979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26528196238984251574617305 19896147179238188680962979)
      ·
        refine ⟨29844220768857283021444469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19896147179238188680962979 29844220768857283021444469)
        ·
          refine ⟨2797895697080370283260419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29844220768857283021444469 2797895697080370283260419)
          ·
            refine ⟨4196843545620555424890629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2797895697080370283260419 4196843545620555424890629)
            ·
              refine ⟨786908164803854142166993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4196843545620555424890629 786908164803854142166993)
              ·
                refine ⟨590181123602890606625245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 786908164803854142166993 590181123602890606625245)
                ·
                  refine ⟨221317921351083977484467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 590181123602890606625245 221317921351083977484467)
                  ·
                    rfl

theorem cell21_969784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 2, 3].length) (baseStart_969784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_969784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_969784 prefixEnd_969784 := by exact prefixLift 969784
  have htrace : WordTrace (prefixWord ++ tailWord_969784) baseStart_969784 baseEnd_969784 := by
    simpa [prefixWord, tailWord_969784, baseEnd_969784] using wordTrace_append hprefix tailTrace_969784
  have hstable : (prefixWord ++ tailWord_969784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969784).length < 2 ^ (prefixWord ++ tailWord_969784).sum := by decide
  have hdescent : baseEnd_969784 < baseStart_969784 := by decide
  rcases family_descends (prefixWord ++ tailWord_969784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969809 : List Nat := [1, 2, 2, 1, 3, 1, 3, 1, 7]
def baseStart_969809 : Nat := 118140960795 + 969809 * 2 ^ 59
def prefixEnd_969809 : Nat := 4983230072969 + 3 ^ 40 * 969809 * 2
def baseEnd_969809 : Nat := 221323626691689489567749

theorem tailTrace_969809 : CollatzResearch.WordTrace tailWord_969809 prefixEnd_969809 221323626691689489567749 := by
  unfold tailWord_969809
  simp only [CollatzResearch.WordTrace]
  refine ⟨35371840143555098035816481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23581226762370065357210987 35371840143555098035816481)
  ·
    refine ⟨26528880107666323526862361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35371840143555098035816481 26528880107666323526862361)
    ·
      refine ⟨19896660080749742645146771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26528880107666323526862361 19896660080749742645146771)
      ·
        refine ⟨29844990121124613967720157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19896660080749742645146771 29844990121124613967720157)
        ·
          refine ⟨11191871295421730237895059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29844990121124613967720157 11191871295421730237895059)
          ·
            refine ⟨16787806943132595356842589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11191871295421730237895059 16787806943132595356842589)
            ·
              refine ⟨6295427603674723258815971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16787806943132595356842589 6295427603674723258815971)
              ·
                refine ⟨9443141405512084888223957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6295427603674723258815971 9443141405512084888223957)
                ·
                  refine ⟨221323626691689489567749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9443141405512084888223957 221323626691689489567749)
                  ·
                    rfl

theorem cell21_969809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 7].length) (baseStart_969809 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_969809 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_969809 prefixEnd_969809 := by exact prefixLift 969809
  have htrace : WordTrace (prefixWord ++ tailWord_969809) baseStart_969809 baseEnd_969809 := by
    simpa [prefixWord, tailWord_969809, baseEnd_969809] using wordTrace_append hprefix tailTrace_969809
  have hstable : (prefixWord ++ tailWord_969809).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969809).length < 2 ^ (prefixWord ++ tailWord_969809).sum := by decide
  have hdescent : baseEnd_969809 < baseStart_969809 := by decide
  rcases family_descends (prefixWord ++ tailWord_969809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969832 : List Nat := [2, 1, 4, 4, 2, 1, 1, 2, 4]
def baseStart_969832 : Nat := 118140960795 + 969832 * 2 ^ 59
def prefixEnd_969832 : Nat := 4983230072969 + 3 ^ 40 * 969832 * 2
def baseEnd_969832 : Nat := 221328875605046560684369

theorem tailTrace_969832 : CollatzResearch.WordTrace tailWord_969832 prefixEnd_969832 221328875605046560684369 := by
  unfold tailWord_969832
  simp only [CollatzResearch.WordTrace]
  refine ⟨17686339511235886481951875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23581786014981181975935833 17686339511235886481951875)
  ·
    refine ⟨26529509266853829722927813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17686339511235886481951875 26529509266853829722927813)
    ·
      refine ⟨4974282987535093073048965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26529509266853829722927813 4974282987535093073048965)
      ·
        refine ⟨932678060162829951196681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4974282987535093073048965 932678060162829951196681)
        ·
          refine ⟨699508545122122463397511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 932678060162829951196681 699508545122122463397511)
          ·
            refine ⟨1049262817683183695096267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699508545122122463397511 1049262817683183695096267)
            ·
              refine ⟨1573894226524775542644401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1049262817683183695096267 1573894226524775542644401)
              ·
                refine ⟨1180420669893581656983301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1573894226524775542644401 1180420669893581656983301)
                ·
                  refine ⟨221328875605046560684369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1180420669893581656983301 221328875605046560684369)
                  ·
                    rfl

theorem cell21_969832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 2, 4].length) (baseStart_969832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_969832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_969832 prefixEnd_969832 := by exact prefixLift 969832
  have htrace : WordTrace (prefixWord ++ tailWord_969832) baseStart_969832 baseEnd_969832 := by
    simpa [prefixWord, tailWord_969832, baseEnd_969832] using wordTrace_append hprefix tailTrace_969832
  have hstable : (prefixWord ++ tailWord_969832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969832).length < 2 ^ (prefixWord ++ tailWord_969832).sum := by decide
  have hdescent : baseEnd_969832 < baseStart_969832 := by decide
  rcases family_descends (prefixWord ++ tailWord_969832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969840 : List Nat := [2, 1, 1, 1, 5, 1, 3, 1, 6]
def baseStart_969840 : Nat := 118140960795 + 969840 * 2 ^ 59
def prefixEnd_969840 : Nat := 4983230072969 + 3 ^ 40 * 969840 * 2
def baseEnd_969840 : Nat := 221330701314040324551019

theorem tailTrace_969840 : CollatzResearch.WordTrace tailWord_969840 prefixEnd_969840 221330701314040324551019 := by
  unfold tailWord_969840
  simp only [CollatzResearch.WordTrace]
  refine ⟨17686485403221395165097487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23581980537628526886796649 17686485403221395165097487)
  ·
    refine ⟨26529728104832092747646231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17686485403221395165097487 26529728104832092747646231)
    ·
      refine ⟨39794592157248139121469347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26529728104832092747646231 39794592157248139121469347)
      ·
        refine ⟨59691888235872208682204021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39794592157248139121469347 59691888235872208682204021)
        ·
          refine ⟨5596114522113019563956627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59691888235872208682204021 5596114522113019563956627)
          ·
            refine ⟨8394171783169529345934941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5596114522113019563956627 8394171783169529345934941)
            ·
              refine ⟨3147814418688573504725603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8394171783169529345934941 3147814418688573504725603)
              ·
                refine ⟨4721721628032860257088405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3147814418688573504725603 4721721628032860257088405)
                ·
                  refine ⟨221330701314040324551019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4721721628032860257088405 221330701314040324551019)
                  ·
                    rfl

theorem cell21_969840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 6].length) (baseStart_969840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_969840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_969840 prefixEnd_969840 := by exact prefixLift 969840
  have htrace : WordTrace (prefixWord ++ tailWord_969840) baseStart_969840 baseEnd_969840 := by
    simpa [prefixWord, tailWord_969840, baseEnd_969840] using wordTrace_append hprefix tailTrace_969840
  have hstable : (prefixWord ++ tailWord_969840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969840).length < 2 ^ (prefixWord ++ tailWord_969840).sum := by decide
  have hdescent : baseEnd_969840 < baseStart_969840 := by decide
  rcases family_descends (prefixWord ++ tailWord_969840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_969995 : List Nat := [1, 1, 1, 1, 5, 4, 2, 3, 3]
def baseStart_969995 : Nat := 118140960795 + 969995 * 2 ^ 59
def prefixEnd_969995 : Nat := 4983230072969 + 3 ^ 40 * 969995 * 2
def baseEnd_969995 : Nat := 221366074425794499467369

theorem tailTrace_969995 : CollatzResearch.WordTrace tailWord_969995 prefixEnd_969995 221366074425794499467369 := by
  unfold tailWord_969995
  simp only [CollatzResearch.WordTrace]
  refine ⟨35378624120881251802087439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23585749413920834534724959 35378624120881251802087439)
  ·
    refine ⟨53067936181321877703131159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35378624120881251802087439 53067936181321877703131159)
    ·
      refine ⟨79601904271982816554696739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53067936181321877703131159 79601904271982816554696739)
      ·
        refine ⟨119402856407974224832045109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79601904271982816554696739 119402856407974224832045109)
        ·
          refine ⟨11194017788247583578004229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119402856407974224832045109 11194017788247583578004229)
          ·
            refine ⟨2098878335296421920875793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11194017788247583578004229 2098878335296421920875793)
            ·
              refine ⟨1574158751472316440656845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2098878335296421920875793 1574158751472316440656845)
              ·
                refine ⟨590309531802118665246317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1574158751472316440656845 590309531802118665246317)
                ·
                  refine ⟨221366074425794499467369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 590309531802118665246317 221366074425794499467369)
                  ·
                    rfl

theorem cell21_969995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 3, 3].length) (baseStart_969995 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_969995 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_969995 prefixEnd_969995 := by exact prefixLift 969995
  have htrace : WordTrace (prefixWord ++ tailWord_969995) baseStart_969995 baseEnd_969995 := by
    simpa [prefixWord, tailWord_969995, baseEnd_969995] using wordTrace_append hprefix tailTrace_969995
  have hstable : (prefixWord ++ tailWord_969995).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_969995).length < 2 ^ (prefixWord ++ tailWord_969995).sum := by decide
  have hdescent : baseEnd_969995 < baseStart_969995 := by decide
  rcases family_descends (prefixWord ++ tailWord_969995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970068 : List Nat := [2, 4, 1, 1, 2, 1, 1, 3, 6]
def baseStart_970068 : Nat := 118140960795 + 970068 * 2 ^ 59
def prefixEnd_970068 : Nat := 4983230072969 + 3 ^ 40 * 970068 * 2
def baseEnd_970068 : Nat := 221382734020362594750553

theorem tailTrace_970068 : CollatzResearch.WordTrace tailWord_970068 prefixEnd_970068 221382734020362594750553 := by
  unfold tailWord_970068
  simp only [CollatzResearch.WordTrace]
  refine ⟨17690643324808392634747429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23587524433077856846329905 17690643324808392634747429)
  ·
    refine ⟨3316995623401573619015143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17690643324808392634747429 3316995623401573619015143)
    ·
      refine ⟨4975493435102360428522715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3316995623401573619015143 4975493435102360428522715)
      ·
        refine ⟨7463240152653540642784073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4975493435102360428522715 7463240152653540642784073)
        ·
          refine ⟨5597430114490155482088055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7463240152653540642784073 5597430114490155482088055)
          ·
            refine ⟨8396145171735233223132083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5597430114490155482088055 8396145171735233223132083)
            ·
              refine ⟨12594217757602849834698125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8396145171735233223132083 12594217757602849834698125)
              ·
                refine ⟨4722831659101068688011797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12594217757602849834698125 4722831659101068688011797)
                ·
                  refine ⟨221382734020362594750553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4722831659101068688011797 221382734020362594750553)
                  ·
                    rfl

theorem cell21_970068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_970068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_970068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_970068 prefixEnd_970068 := by exact prefixLift 970068
  have htrace : WordTrace (prefixWord ++ tailWord_970068) baseStart_970068 baseEnd_970068 := by
    simpa [prefixWord, tailWord_970068, baseEnd_970068] using wordTrace_append hprefix tailTrace_970068
  have hstable : (prefixWord ++ tailWord_970068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970068).length < 2 ^ (prefixWord ++ tailWord_970068).sum := by decide
  have hdescent : baseEnd_970068 < baseStart_970068 := by decide
  rcases family_descends (prefixWord ++ tailWord_970068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970077 : List Nat := [1, 4, 5, 1, 1, 2, 2, 1, 4]
def baseStart_970077 : Nat := 118140960795 + 970077 * 2 ^ 59
def prefixEnd_970077 : Nat := 4983230072969 + 3 ^ 40 * 970077 * 2
def baseEnd_970077 : Nat := 221384787942980579100535

theorem tailTrace_970077 : CollatzResearch.WordTrace tailWord_970077 prefixEnd_970077 221384787942980579100535 := by
  unfold tailWord_970077
  simp only [CollatzResearch.WordTrace]
  refine ⟨35381614906584179806572485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23587743271056119871048323 35381614906584179806572485)
  ·
    refine ⟨6634052794984533713732341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35381614906584179806572485 6634052794984533713732341)
    ·
      refine ⟨621942449529800035662407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6634052794984533713732341 621942449529800035662407)
      ·
        refine ⟨932913674294700053493611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621942449529800035662407 932913674294700053493611)
        ·
          refine ⟨1399370511442050080240417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 932913674294700053493611 1399370511442050080240417)
          ·
            refine ⟨1049527883581537560180313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1399370511442050080240417 1049527883581537560180313)
            ·
              refine ⟨787145912686153170135235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1049527883581537560180313 787145912686153170135235)
              ·
                refine ⟨1180718869029229755202853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 787145912686153170135235 1180718869029229755202853)
                ·
                  refine ⟨221384787942980579100535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1180718869029229755202853 221384787942980579100535)
                  ·
                    rfl

theorem cell21_970077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 1, 4].length) (baseStart_970077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_970077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_970077 prefixEnd_970077 := by exact prefixLift 970077
  have htrace : WordTrace (prefixWord ++ tailWord_970077) baseStart_970077 baseEnd_970077 := by
    simpa [prefixWord, tailWord_970077, baseEnd_970077] using wordTrace_append hprefix tailTrace_970077
  have hstable : (prefixWord ++ tailWord_970077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970077).length < 2 ^ (prefixWord ++ tailWord_970077).sum := by decide
  have hdescent : baseEnd_970077 < baseStart_970077 := by decide
  rcases family_descends (prefixWord ++ tailWord_970077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970144 : List Nat := [2, 1, 1, 4, 1, 2, 1, 5, 4]
def baseStart_970144 : Nat := 118140960795 + 970144 * 2 ^ 59
def prefixEnd_970144 : Nat := 4983230072969 + 3 ^ 40 * 970144 * 2
def baseEnd_970144 : Nat := 221400078255803351483731

theorem tailTrace_970144 : CollatzResearch.WordTrace tailWord_970144 prefixEnd_970144 221400078255803351483731 := by
  unfold tailWord_970144
  simp only [CollatzResearch.WordTrace]
  refine ⟨17692029298670725124630743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23589372398227633499507657 17692029298670725124630743)
  ·
    refine ⟨26538043948006087686946115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17692029298670725124630743 26538043948006087686946115)
    ·
      refine ⟨39807065922009131530419173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26538043948006087686946115 39807065922009131530419173)
      ·
        refine ⟨7463824860376712161953595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39807065922009131530419173 7463824860376712161953595)
        ·
          refine ⟨11195737290565068242930393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7463824860376712161953595 11195737290565068242930393)
          ·
            refine ⟨8396802967923801182197795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11195737290565068242930393 8396802967923801182197795)
            ·
              refine ⟨12595204451885701773296693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8396802967923801182197795 12595204451885701773296693)
              ·
                refine ⟨1180800417364284541246565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12595204451885701773296693 1180800417364284541246565)
                ·
                  refine ⟨221400078255803351483731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1180800417364284541246565 221400078255803351483731)
                  ·
                    rfl

theorem cell21_970144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5, 4].length) (baseStart_970144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_970144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_970144 prefixEnd_970144 := by exact prefixLift 970144
  have htrace : WordTrace (prefixWord ++ tailWord_970144) baseStart_970144 baseEnd_970144 := by
    simpa [prefixWord, tailWord_970144, baseEnd_970144] using wordTrace_append hprefix tailTrace_970144
  have hstable : (prefixWord ++ tailWord_970144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970144).length < 2 ^ (prefixWord ++ tailWord_970144).sum := by decide
  have hdescent : baseEnd_970144 < baseStart_970144 := by decide
  rcases family_descends (prefixWord ++ tailWord_970144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970246 : List Nat := [6, 2, 1, 1, 3, 1, 2, 1, 4]
def baseStart_970246 : Nat := 118140960795 + 970246 * 2 ^ 59
def prefixEnd_970246 : Nat := 4983230072969 + 3 ^ 40 * 970246 * 2
def baseEnd_970246 : Nat := 221423356045473840783523

theorem tailTrace_970246 : CollatzResearch.WordTrace tailWord_970246 prefixEnd_970246 221423356045473840783523 := by
  unfold tailWord_970246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1105868088842872552171081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23591852561981281112983061 1105868088842872552171081)
  ·
    refine ⟨829401066632154414128311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1105868088842872552171081 829401066632154414128311)
    ·
      refine ⟨1244101599948231621192467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 829401066632154414128311 1244101599948231621192467)
      ·
        refine ⟨1866152399922347431788701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1244101599948231621192467 1866152399922347431788701)
        ·
          refine ⟨699807149970880286920763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1866152399922347431788701 699807149970880286920763)
          ·
            refine ⟨1049710724956320430381145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699807149970880286920763 1049710724956320430381145)
            ·
              refine ⟨787283043717240322785859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1049710724956320430381145 787283043717240322785859)
              ·
                refine ⟨1180924565575860484178789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 787283043717240322785859 1180924565575860484178789)
                ·
                  refine ⟨221423356045473840783523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1180924565575860484178789 221423356045473840783523)
                  ·
                    rfl

theorem cell21_970246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_970246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_970246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_970246 prefixEnd_970246 := by exact prefixLift 970246
  have htrace : WordTrace (prefixWord ++ tailWord_970246) baseStart_970246 baseEnd_970246 := by
    simpa [prefixWord, tailWord_970246, baseEnd_970246] using wordTrace_append hprefix tailTrace_970246
  have hstable : (prefixWord ++ tailWord_970246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970246).length < 2 ^ (prefixWord ++ tailWord_970246).sum := by decide
  have hdescent : baseEnd_970246 < baseStart_970246 := by decide
  rcases family_descends (prefixWord ++ tailWord_970246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970251 : List Nat := [1, 1, 1, 1, 8, 1, 2, 6]
def baseStart_970251 : Nat := 118140960795 + 970251 * 2 ^ 59
def prefixEnd_970251 : Nat := 4983230072969 + 3 ^ 40 * 970251 * 2
def baseEnd_970251 : Nat := 73808165704531647733393

theorem tailTrace_970251 : CollatzResearch.WordTrace tailWord_970251 prefixEnd_970251 73808165704531647733393 := by
  unfold tailWord_970251
  simp only [CollatzResearch.WordTrace]
  refine ⟨35387961207953807523406607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23591974138635871682271071 35387961207953807523406607)
  ·
    refine ⟨53081941811930711285109911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35387961207953807523406607 53081941811930711285109911)
    ·
      refine ⟨79622912717896066927664867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53081941811930711285109911 79622912717896066927664867)
      ·
        refine ⟨119434369076844100391497301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79622912717896066927664867 119434369076844100391497301)
        ·
          refine ⟨1399621512619266801462859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 119434369076844100391497301 1399621512619266801462859)
          ·
            refine ⟨2099432268928900202194289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1399621512619266801462859 2099432268928900202194289)
            ·
              refine ⟨1574574201696675151645717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2099432268928900202194289 1574574201696675151645717)
              ·
                refine ⟨73808165704531647733393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1574574201696675151645717 73808165704531647733393)
                ·
                  rfl

theorem cell21_970251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 6].length) (baseStart_970251 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_970251 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_970251 prefixEnd_970251 := by exact prefixLift 970251
  have htrace : WordTrace (prefixWord ++ tailWord_970251) baseStart_970251 baseEnd_970251 := by
    simpa [prefixWord, tailWord_970251, baseEnd_970251] using wordTrace_append hprefix tailTrace_970251
  have hstable : (prefixWord ++ tailWord_970251).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970251).length < 2 ^ (prefixWord ++ tailWord_970251).sum := by decide
  have hdescent : baseEnd_970251 < baseStart_970251 := by decide
  rcases family_descends (prefixWord ++ tailWord_970251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970296 : List Nat := [2, 1, 2, 1, 4, 2, 1, 4, 4]
def baseStart_970296 : Nat := 118140960795 + 970296 * 2 ^ 59
def prefixEnd_970296 : Nat := 4983230072969 + 3 ^ 40 * 970296 * 2
def baseEnd_970296 : Nat := 221434766726684864950087

theorem tailTrace_970296 : CollatzResearch.WordTrace tailWord_970296 prefixEnd_970296 221434766726684864950087 := by
  unfold tailWord_970296
  simp only [CollatzResearch.WordTrace]
  refine ⟨17694801246395390104397371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23593068328527186805863161 17694801246395390104397371)
  ·
    refine ⟨26542201869593085156596057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17694801246395390104397371 26542201869593085156596057)
    ·
      refine ⟨19906651402194813867447043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26542201869593085156596057 19906651402194813867447043)
      ·
        refine ⟨29859977103292220801170565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19906651402194813867447043 29859977103292220801170565)
        ·
          refine ⟨5598745706867291400219481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29859977103292220801170565 5598745706867291400219481)
          ·
            refine ⟨4199059280150468550164611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5598745706867291400219481 4199059280150468550164611)
            ·
              refine ⟨6298588920225702825246917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4199059280150468550164611 6298588920225702825246917)
              ·
                refine ⟨1180985422542319279733797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6298588920225702825246917 1180985422542319279733797)
                ·
                  refine ⟨221434766726684864950087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1180985422542319279733797 221434766726684864950087)
                  ·
                    rfl

theorem cell21_970296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4, 4].length) (baseStart_970296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_970296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_970296 prefixEnd_970296 := by exact prefixLift 970296
  have htrace : WordTrace (prefixWord ++ tailWord_970296) baseStart_970296 baseEnd_970296 := by
    simpa [prefixWord, tailWord_970296, baseEnd_970296] using wordTrace_append hprefix tailTrace_970296
  have hstable : (prefixWord ++ tailWord_970296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970296).length < 2 ^ (prefixWord ++ tailWord_970296).sum := by decide
  have hdescent : baseEnd_970296 < baseStart_970296 := by decide
  rcases family_descends (prefixWord ++ tailWord_970296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970327 : List Nat := [1, 1, 3, 2, 2, 4, 3, 5]
def baseStart_970327 : Nat := 118140960795 + 970327 * 2 ^ 59
def prefixEnd_970327 : Nat := 4983230072969 + 3 ^ 40 * 970327 * 2
def baseEnd_970327 : Nat := 73813947116345233311119

theorem tailTrace_970327 : CollatzResearch.WordTrace tailWord_970327 prefixEnd_970327 73813947116345233311119 := by
  unfold tailWord_970327
  simp only [CollatzResearch.WordTrace]
  refine ⟨35390733155678472503173235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23593822103785648335448823 35390733155678472503173235)
  ·
    refine ⟨53086099733517708754759853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35390733155678472503173235 53086099733517708754759853)
    ·
      refine ⟨19907287400069140783034945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53086099733517708754759853 19907287400069140783034945)
      ·
        refine ⟨14930465550051855587276209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19907287400069140783034945 14930465550051855587276209)
        ·
          refine ⟨11197849162538891690457157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14930465550051855587276209 11197849162538891690457157)
          ·
            refine ⟨2099596717976042191960717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11197849162538891690457157 2099596717976042191960717)
            ·
              refine ⟨787348769241015821985269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2099596717976042191960717 787348769241015821985269)
              ·
                refine ⟨73813947116345233311119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 787348769241015821985269 73813947116345233311119)
                ·
                  rfl

theorem cell21_970327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 5].length) (baseStart_970327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_970327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_970327 prefixEnd_970327 := by exact prefixLift 970327
  have htrace : WordTrace (prefixWord ++ tailWord_970327) baseStart_970327 baseEnd_970327 := by
    simpa [prefixWord, tailWord_970327, baseEnd_970327] using wordTrace_append hprefix tailTrace_970327
  have hstable : (prefixWord ++ tailWord_970327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970327).length < 2 ^ (prefixWord ++ tailWord_970327).sum := by decide
  have hdescent : baseEnd_970327 < baseStart_970327 := by decide
  rcases family_descends (prefixWord ++ tailWord_970327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970333 : List Nat := [1, 4, 4, 2, 1, 1, 2, 3, 3]
def baseStart_970333 : Nat := 118140960795 + 970333 * 2 ^ 59
def prefixEnd_970333 : Nat := 4983230072969 + 3 ^ 40 * 970333 * 2
def baseEnd_970333 : Nat := 221443210630781022833345

theorem tailTrace_970333 : CollatzResearch.WordTrace tailWord_970333 prefixEnd_970333 221443210630781022833345 := by
  unfold tailWord_970333
  simp only [CollatzResearch.WordTrace]
  refine ⟨35390951993656735527891653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23593967995771157018594435 35390951993656735527891653)
  ·
    refine ⟨6635803498810637911479685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35390951993656735527891653 6635803498810637911479685)
    ·
      refine ⟨1244213156026994608402441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6635803498810637911479685 1244213156026994608402441)
      ·
        refine ⟨933159867020245956301831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1244213156026994608402441 933159867020245956301831)
        ·
          refine ⟨1399739800530368934452747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 933159867020245956301831 1399739800530368934452747)
          ·
            refine ⟨2099609700795553401679121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1399739800530368934452747 2099609700795553401679121)
            ·
              refine ⟨1574707275596665051259341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2099609700795553401679121 1574707275596665051259341)
              ·
                refine ⟨590515228348749394222253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1574707275596665051259341 590515228348749394222253)
                ·
                  refine ⟨221443210630781022833345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 590515228348749394222253 221443210630781022833345)
                  ·
                    rfl

theorem cell21_970333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 3, 3].length) (baseStart_970333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_970333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_970333 prefixEnd_970333 := by exact prefixLift 970333
  have htrace : WordTrace (prefixWord ++ tailWord_970333) baseStart_970333 baseEnd_970333 := by
    simpa [prefixWord, tailWord_970333, baseEnd_970333] using wordTrace_append hprefix tailTrace_970333
  have hstable : (prefixWord ++ tailWord_970333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970333).length < 2 ^ (prefixWord ++ tailWord_970333).sum := by decide
  have hdescent : baseEnd_970333 < baseStart_970333 := by decide
  rcases family_descends (prefixWord ++ tailWord_970333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970358 : List Nat := [5, 1, 1, 2, 2, 1, 1, 3, 5]
def baseStart_970358 : Nat := 118140960795 + 970358 * 2 ^ 59
def prefixEnd_970358 : Nat := 4983230072969 + 3 ^ 40 * 970358 * 2
def baseEnd_970358 : Nat := 221448915971386534916627

theorem tailTrace_970358 : CollatzResearch.WordTrace tailWord_970358 prefixEnd_970358 221448915971386534916627 := by
  unfold tailWord_970358
  simp only [CollatzResearch.WordTrace]
  refine ⟨2211991488660385299846983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23594575879044109865034485 2211991488660385299846983)
  ·
    refine ⟨3317987232990577949770475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2211991488660385299846983 3317987232990577949770475)
    ·
      refine ⟨4976980849485866924655713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3317987232990577949770475 4976980849485866924655713)
      ·
        refine ⟨3732735637114400193491785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4976980849485866924655713 3732735637114400193491785)
        ·
          refine ⟨2799551727835800145118839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3732735637114400193491785 2799551727835800145118839)
          ·
            refine ⟨4199327591753700217678259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2799551727835800145118839 4199327591753700217678259)
            ·
              refine ⟨6298991387630550326517389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4199327591753700217678259 6298991387630550326517389)
              ·
                refine ⟨2362121770361456372444021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6298991387630550326517389 2362121770361456372444021)
                ·
                  refine ⟨221448915971386534916627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2362121770361456372444021 221448915971386534916627)
                  ·
                    rfl

theorem cell21_970358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_970358 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_970358 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_970358 prefixEnd_970358 := by exact prefixLift 970358
  have htrace : WordTrace (prefixWord ++ tailWord_970358) baseStart_970358 baseEnd_970358 := by
    simpa [prefixWord, tailWord_970358, baseEnd_970358] using wordTrace_append hprefix tailTrace_970358
  have hstable : (prefixWord ++ tailWord_970358).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970358).length < 2 ^ (prefixWord ++ tailWord_970358).sum := by decide
  have hdescent : baseEnd_970358 < baseStart_970358 := by decide
  rcases family_descends (prefixWord ++ tailWord_970358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970465 : List Nat := [1, 2, 3, 1, 5, 1, 2, 2, 4]
def baseStart_970465 : Nat := 118140960795 + 970465 * 2 ^ 59
def prefixEnd_970465 : Nat := 4983230072969 + 3 ^ 40 * 970465 * 2
def baseEnd_970465 : Nat := 221473334829178126633075

theorem tailTrace_970465 : CollatzResearch.WordTrace tailWord_970465 prefixEnd_970465 221473334829178126633075 := by
  unfold tailWord_970465
  simp only [CollatzResearch.WordTrace]
  refine ⟨35395766429178522071696849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23597177619452348047797899 35395766429178522071696849)
  ·
    refine ⟨26546824821883891553772637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35395766429178522071696849 26546824821883891553772637)
    ·
      refine ⟨9955059308206459332664739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26546824821883891553772637 9955059308206459332664739)
      ·
        refine ⟨14932588962309688998997109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9955059308206459332664739 14932588962309688998997109)
        ·
          refine ⟨1399930215216533343655979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14932588962309688998997109 1399930215216533343655979)
          ·
            refine ⟨2099895322824800015483969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1399930215216533343655979 2099895322824800015483969)
            ·
              refine ⟨1574921492118600011612977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2099895322824800015483969 1574921492118600011612977)
              ·
                refine ⟨1181191119088950008709733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1574921492118600011612977 1181191119088950008709733)
                ·
                  refine ⟨221473334829178126633075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1181191119088950008709733 221473334829178126633075)
                  ·
                    rfl

theorem cell21_970465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2, 4].length) (baseStart_970465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_970465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_970465 prefixEnd_970465 := by exact prefixLift 970465
  have htrace : WordTrace (prefixWord ++ tailWord_970465) baseStart_970465 baseEnd_970465 := by
    simpa [prefixWord, tailWord_970465, baseEnd_970465] using wordTrace_append hprefix tailTrace_970465
  have hstable : (prefixWord ++ tailWord_970465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970465).length < 2 ^ (prefixWord ++ tailWord_970465).sum := by decide
  have hdescent : baseEnd_970465 < baseStart_970465 := by decide
  rcases family_descends (prefixWord ++ tailWord_970465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970510 : List Nat := [4, 1, 1, 2, 1, 1, 3, 5, 3]
def baseStart_970510 : Nat := 118140960795 + 970510 * 2 ^ 59
def prefixEnd_970510 : Nat := 4983230072969 + 3 ^ 40 * 970510 * 2
def baseEnd_970510 : Nat := 221483604442268048382983

theorem tailTrace_970510 : CollatzResearch.WordTrace tailWord_970510 prefixEnd_970510 221483604442268048382983 := by
  unfold tailWord_970510
  simp only [CollatzResearch.WordTrace]
  refine ⟨4424675964251936844635623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23598271809343663171389989 4424675964251936844635623)
  ·
    refine ⟨6637013946377905266953435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4424675964251936844635623 6637013946377905266953435)
    ·
      refine ⟨9955520919566857900430153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6637013946377905266953435 9955520919566857900430153)
      ·
        refine ⟨7466640689675143425322615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9955520919566857900430153 7466640689675143425322615)
        ·
          refine ⟨11199961034512715137983923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7466640689675143425322615 11199961034512715137983923)
          ·
            refine ⟨16799941551769072706975885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11199961034512715137983923 16799941551769072706975885)
            ·
              refine ⟨6299978081913402265115957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16799941551769072706975885 6299978081913402265115957)
              ·
                refine ⟨590622945179381462354621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6299978081913402265115957 590622945179381462354621)
                ·
                  refine ⟨221483604442268048382983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 590622945179381462354621 221483604442268048382983)
                  ·
                    rfl

theorem cell21_970510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 5, 3].length) (baseStart_970510 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_970510 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_970510 prefixEnd_970510 := by exact prefixLift 970510
  have htrace : WordTrace (prefixWord ++ tailWord_970510) baseStart_970510 baseEnd_970510 := by
    simpa [prefixWord, tailWord_970510, baseEnd_970510] using wordTrace_append hprefix tailTrace_970510
  have hstable : (prefixWord ++ tailWord_970510).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970510).length < 2 ^ (prefixWord ++ tailWord_970510).sum := by decide
  have hdescent : baseEnd_970510 < baseStart_970510 := by decide
  rcases family_descends (prefixWord ++ tailWord_970510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970516 : List Nat := [2, 4, 4, 1, 1, 2, 1, 2, 4]
def baseStart_970516 : Nat := 118140960795 + 970516 * 2 ^ 59
def prefixEnd_970516 : Nat := 4983230072969 + 3 ^ 40 * 970516 * 2
def baseEnd_970516 : Nat := 221484973724013371282971

theorem tailTrace_970516 : CollatzResearch.WordTrace tailWord_970516 prefixEnd_970516 221484973724013371282971 := by
  unfold tailWord_970516
  simp only [CollatzResearch.WordTrace]
  refine ⟨17698813275996878890901701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23598417701329171854535601 17698813275996878890901701)
  ·
    refine ⟨3318527489249414792044069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17698813275996878890901701 3318527489249414792044069)
    ·
      refine ⟨622223904234265273508263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3318527489249414792044069 622223904234265273508263)
      ·
        refine ⟨933335856351397910262395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622223904234265273508263 933335856351397910262395)
        ·
          refine ⟨1400003784527096865393593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 933335856351397910262395 1400003784527096865393593)
          ·
            refine ⟨1050002838395322649045195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1400003784527096865393593 1050002838395322649045195)
            ·
              refine ⟨1575004257592983973567793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1050002838395322649045195 1575004257592983973567793)
              ·
                refine ⟨1181253193194737980175845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1575004257592983973567793 1181253193194737980175845)
                ·
                  refine ⟨221484973724013371282971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1181253193194737980175845 221484973724013371282971)
                  ·
                    rfl

theorem cell21_970516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_970516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_970516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_970516 prefixEnd_970516 := by exact prefixLift 970516
  have htrace : WordTrace (prefixWord ++ tailWord_970516) baseStart_970516 baseEnd_970516 := by
    simpa [prefixWord, tailWord_970516, baseEnd_970516] using wordTrace_append hprefix tailTrace_970516
  have hstable : (prefixWord ++ tailWord_970516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970516).length < 2 ^ (prefixWord ++ tailWord_970516).sum := by decide
  have hdescent : baseEnd_970516 < baseStart_970516 := by decide
  rcases family_descends (prefixWord ++ tailWord_970516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970600 : List Nat := [2, 1, 4, 2, 1, 1, 3, 3, 4]
def baseStart_970600 : Nat := 118140960795 + 970600 * 2 ^ 59
def prefixEnd_970600 : Nat := 4983230072969 + 3 ^ 40 * 970600 * 2
def baseEnd_970600 : Nat := 221504143668447891882799

theorem tailTrace_970600 : CollatzResearch.WordTrace tailWord_970600 prefixEnd_970600 221504143668447891882799 := by
  unfold tailWord_970600
  simp only [CollatzResearch.WordTrace]
  refine ⟨17700345141844720063930627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23600460189126293418574169 17700345141844720063930627)
  ·
    refine ⟨26550517712767080095895941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17700345141844720063930627 26550517712767080095895941)
    ·
      refine ⟨4978222071143827517980489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26550517712767080095895941 4978222071143827517980489)
      ·
        refine ⟨3733666553357870638485367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4978222071143827517980489 3733666553357870638485367)
        ·
          refine ⟨5600499830036805957728051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3733666553357870638485367 5600499830036805957728051)
          ·
            refine ⟨8400749745055208936592077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5600499830036805957728051 8400749745055208936592077)
            ·
              refine ⟨3150281154395703351222029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8400749745055208936592077 3150281154395703351222029)
              ·
                refine ⟨1181355432898388756708261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3150281154395703351222029 1181355432898388756708261)
                ·
                  refine ⟨221504143668447891882799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1181355432898388756708261 221504143668447891882799)
                  ·
                    rfl

theorem cell21_970600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3, 4].length) (baseStart_970600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_970600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_970600 prefixEnd_970600 := by exact prefixLift 970600
  have htrace : WordTrace (prefixWord ++ tailWord_970600) baseStart_970600 baseEnd_970600 := by
    simpa [prefixWord, tailWord_970600, baseEnd_970600] using wordTrace_append hprefix tailTrace_970600
  have hstable : (prefixWord ++ tailWord_970600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970600).length < 2 ^ (prefixWord ++ tailWord_970600).sum := by decide
  have hdescent : baseEnd_970600 < baseStart_970600 := by decide
  rcases family_descends (prefixWord ++ tailWord_970600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970648 : List Nat := [2, 1, 2, 6, 1, 2, 1, 6]
def baseStart_970648 : Nat := 118140960795 + 970648 * 2 ^ 59
def prefixEnd_970648 : Nat := 4983230072969 + 3 ^ 40 * 970648 * 2
def baseEnd_970648 : Nat := 73838365974136825027567

theorem tailTrace_970648 : CollatzResearch.WordTrace tailWord_970648 prefixEnd_970648 73838365974136825027567 := by
  unfold tailWord_970648
  simp only [CollatzResearch.WordTrace]
  refine ⟨17701220493757772162804299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23601627325010362883739065 17701220493757772162804299)
  ·
    refine ⟨26551830740636658244206449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17701220493757772162804299 26551830740636658244206449)
    ·
      refine ⟨19913873055477493683154837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26551830740636658244206449 19913873055477493683154837)
      ·
        refine ⟨933462799475507516397883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19913873055477493683154837 933462799475507516397883)
        ·
          refine ⟨1400194199213261274596825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 933462799475507516397883 1400194199213261274596825)
          ·
            refine ⟨1050145649409945955947619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1400194199213261274596825 1050145649409945955947619)
            ·
              refine ⟨1575218474114918933921429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1050145649409945955947619 1575218474114918933921429)
              ·
                refine ⟨73838365974136825027567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1575218474114918933921429 73838365974136825027567)
                ·
                  rfl

theorem cell21_970648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 6].length) (baseStart_970648 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_970648 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_970648 prefixEnd_970648 := by exact prefixLift 970648
  have htrace : WordTrace (prefixWord ++ tailWord_970648) baseStart_970648 baseEnd_970648 := by
    simpa [prefixWord, tailWord_970648, baseEnd_970648] using wordTrace_append hprefix tailTrace_970648
  have hstable : (prefixWord ++ tailWord_970648).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970648).length < 2 ^ (prefixWord ++ tailWord_970648).sum := by decide
  have hdescent : baseEnd_970648 < baseStart_970648 := by decide
  rcases family_descends (prefixWord ++ tailWord_970648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970704 : List Nat := [2, 1, 1, 1, 1, 2, 5, 3, 5]
def baseStart_970704 : Nat := 118140960795 + 970704 * 2 ^ 59
def prefixEnd_970704 : Nat := 4983230072969 + 3 ^ 40 * 970704 * 2
def baseEnd_970704 : Nat := 221527877885366822149253

theorem tailTrace_970704 : CollatzResearch.WordTrace tailWord_970704 prefixEnd_970704 221527877885366822149253 := by
  unfold tailWord_970704
  simp only [CollatzResearch.WordTrace]
  refine ⟨17702241737656332944823583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23602988983541777259764777 17702241737656332944823583)
  ·
    refine ⟨26553362606484499417235375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17702241737656332944823583 26553362606484499417235375)
    ·
      refine ⟨39830043909726749125853063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26553362606484499417235375 39830043909726749125853063)
      ·
        refine ⟨59745065864590123688779595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39830043909726749125853063 59745065864590123688779595)
        ·
          refine ⟨89617598796885185533169393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59745065864590123688779595 89617598796885185533169393)
          ·
            refine ⟨67213199097663889149877045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89617598796885185533169393 67213199097663889149877045)
            ·
              refine ⟨6301237415405989607800973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67213199097663889149877045 6301237415405989607800973)
              ·
                refine ⟨2362964030777246102925365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6301237415405989607800973 2362964030777246102925365)
                ·
                  refine ⟨221527877885366822149253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2362964030777246102925365 221527877885366822149253)
                  ·
                    rfl

theorem cell21_970704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 5].length) (baseStart_970704 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_970704 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_970704 prefixEnd_970704 := by exact prefixLift 970704
  have htrace : WordTrace (prefixWord ++ tailWord_970704) baseStart_970704 baseEnd_970704 := by
    simpa [prefixWord, tailWord_970704, baseEnd_970704] using wordTrace_append hprefix tailTrace_970704
  have hstable : (prefixWord ++ tailWord_970704).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970704).length < 2 ^ (prefixWord ++ tailWord_970704).sum := by decide
  have hdescent : baseEnd_970704 < baseStart_970704 := by decide
  rcases family_descends (prefixWord ++ tailWord_970704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970749 : List Nat := [1, 4, 1, 1, 1, 2, 11]
def baseStart_970749 : Nat := 118140960795 + 970749 * 2 ^ 59
def prefixEnd_970749 : Nat := 4983230072969 + 3 ^ 40 * 970749 * 2
def baseEnd_970749 : Nat := 24615349722050749322129

theorem tailTrace_970749 : CollatzResearch.WordTrace tailWord_970749 prefixEnd_970749 24615349722050749322129 := by
  unfold tailWord_970749
  simp only [CollatzResearch.WordTrace]
  refine ⟨35406124760149638575035301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23604083173433092383356867 35406124760149638575035301)
  ·
    refine ⟨6638648392528057232819119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35406124760149638575035301 6638648392528057232819119)
    ·
      refine ⟨9957972588792085849228679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6638648392528057232819119 9957972588792085849228679)
      ·
        refine ⟨14936958883188128773843019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9957972588792085849228679 14936958883188128773843019)
        ·
          refine ⟨22405438324782193160764529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14936958883188128773843019 22405438324782193160764529)
          ·
            refine ⟨16804078743586644870573397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22405438324782193160764529 16804078743586644870573397)
            ·
              refine ⟨24615349722050749322129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 16804078743586644870573397 24615349722050749322129)
              ·
                rfl

theorem cell21_970749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 11].length) (baseStart_970749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_970749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_970749 prefixEnd_970749 := by exact prefixLift 970749
  have htrace : WordTrace (prefixWord ++ tailWord_970749) baseStart_970749 baseEnd_970749 := by
    simpa [prefixWord, tailWord_970749, baseEnd_970749] using wordTrace_append hprefix tailTrace_970749
  have hstable : (prefixWord ++ tailWord_970749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970749).length < 2 ^ (prefixWord ++ tailWord_970749).sum := by decide
  have hdescent : baseEnd_970749 < baseStart_970749 := by decide
  rcases family_descends (prefixWord ++ tailWord_970749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970758 : List Nat := [6, 2, 1, 2, 1, 1, 2, 6]
def baseStart_970758 : Nat := 118140960795 + 970758 * 2 ^ 59
def prefixEnd_970758 : Nat := 4983230072969 + 3 ^ 40 * 970758 * 2
def baseEnd_970758 : Nat := 73846733807024909416381

theorem tailTrace_970758 : CollatzResearch.WordTrace tailWord_970758 prefixEnd_970758 73846733807024909416381 := by
  unfold tailWord_970758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1106451656784907284753529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23604302011411355408075285 1106451656784907284753529)
  ·
    refine ⟨829838742588680463565147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1106451656784907284753529 829838742588680463565147)
    ·
      refine ⟨1244758113883020695347721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 829838742588680463565147 1244758113883020695347721)
      ·
        refine ⟨933568585412265521510791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1244758113883020695347721 933568585412265521510791)
        ·
          refine ⟨1400352878118398282266187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 933568585412265521510791 1400352878118398282266187)
          ·
            refine ⟨2100529317177597423399281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1400352878118398282266187 2100529317177597423399281)
            ·
              refine ⟨1575396987883198067549461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2100529317177597423399281 1575396987883198067549461)
              ·
                refine ⟨73846733807024909416381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1575396987883198067549461 73846733807024909416381)
                ·
                  rfl

theorem cell21_970758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_970758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_970758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_970758 prefixEnd_970758 := by exact prefixLift 970758
  have htrace : WordTrace (prefixWord ++ tailWord_970758) baseStart_970758 baseEnd_970758 := by
    simpa [prefixWord, tailWord_970758, baseEnd_970758] using wordTrace_append hprefix tailTrace_970758
  have hstable : (prefixWord ++ tailWord_970758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970758).length < 2 ^ (prefixWord ++ tailWord_970758).sum := by decide
  have hdescent : baseEnd_970758 < baseStart_970758 := by decide
  rcases family_descends (prefixWord ++ tailWord_970758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970766 : List Nat := [4, 1, 1, 2, 2, 1, 4, 6]
def baseStart_970766 : Nat := 118140960795 + 970766 * 2 ^ 59
def prefixEnd_970766 : Nat := 4983230072969 + 3 ^ 40 * 970766 * 2
def baseEnd_970766 : Nat := 73847342376689497371931

theorem tailTrace_970766 : CollatzResearch.WordTrace tailWord_970766 prefixEnd_970766 73847342376689497371931 := by
  unfold tailWord_970766
  simp only [CollatzResearch.WordTrace]
  refine ⟨4425843100136006309800519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23604496534058700318936101 4425843100136006309800519)
  ·
    refine ⟨6638764650204009464700779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4425843100136006309800519 6638764650204009464700779)
    ·
      refine ⟨9958146975306014197051169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6638764650204009464700779 9958146975306014197051169)
      ·
        refine ⟨7468610231479510647788377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9958146975306014197051169 7468610231479510647788377)
        ·
          refine ⟨5601457673609632985841283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7468610231479510647788377 5601457673609632985841283)
          ·
            refine ⟨8402186510414449478761925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5601457673609632985841283 8402186510414449478761925)
            ·
              refine ⟨1575409970702709277267861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8402186510414449478761925 1575409970702709277267861)
              ·
                refine ⟨73847342376689497371931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1575409970702709277267861 73847342376689497371931)
                ·
                  rfl

theorem cell21_970766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_970766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_970766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_970766 prefixEnd_970766 := by exact prefixLift 970766
  have htrace : WordTrace (prefixWord ++ tailWord_970766) baseStart_970766 baseEnd_970766 := by
    simpa [prefixWord, tailWord_970766, baseEnd_970766] using wordTrace_append hprefix tailTrace_970766
  have hstable : (prefixWord ++ tailWord_970766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970766).length < 2 ^ (prefixWord ++ tailWord_970766).sum := by decide
  have hdescent : baseEnd_970766 < baseStart_970766 := by decide
  rcases family_descends (prefixWord ++ tailWord_970766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970842 : List Nat := [3, 1, 1, 2, 1, 1, 7, 5]
def baseStart_970842 : Nat := 118140960795 + 970842 * 2 ^ 59
def prefixEnd_970842 : Nat := 4983230072969 + 3 ^ 40 * 970842 * 2
def baseEnd_970842 : Nat := 73853123788503082949657

theorem tailTrace_970842 : CollatzResearch.WordTrace tailWord_970842 prefixEnd_970842 73853123788503082949657 := by
  unfold tailWord_970842
  simp only [CollatzResearch.WordTrace]
  refine ⟨8852379187203178864542695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23606344499208476972113853 8852379187203178864542695)
  ·
    refine ⟨13278568780804768296814043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8852379187203178864542695 13278568780804768296814043)
    ·
      refine ⟨19917853171207152445221065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13278568780804768296814043 19917853171207152445221065)
      ·
        refine ⟨14938389878405364333915799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19917853171207152445221065 14938389878405364333915799)
        ·
          refine ⟨22407584817608046500873699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14938389878405364333915799 22407584817608046500873699)
          ·
            refine ⟨33611377226412069751310549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22407584817608046500873699 33611377226412069751310549)
            ·
              refine ⟨787766653744032884796341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 33611377226412069751310549 787766653744032884796341)
              ·
                refine ⟨73853123788503082949657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 787766653744032884796341 73853123788503082949657)
                ·
                  rfl

theorem cell21_970842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 5].length) (baseStart_970842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_970842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_970842 prefixEnd_970842 := by exact prefixLift 970842
  have htrace : WordTrace (prefixWord ++ tailWord_970842) baseStart_970842 baseEnd_970842 := by
    simpa [prefixWord, tailWord_970842, baseEnd_970842] using wordTrace_append hprefix tailTrace_970842
  have hstable : (prefixWord ++ tailWord_970842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970842).length < 2 ^ (prefixWord ++ tailWord_970842).sum := by decide
  have hdescent : baseEnd_970842 < baseStart_970842 := by decide
  rcases family_descends (prefixWord ++ tailWord_970842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970873 : List Nat := [1, 2, 1, 3, 4, 2, 2, 1, 5]
def baseStart_970873 : Nat := 118140960795 + 970873 * 2 ^ 59
def prefixEnd_970873 : Nat := 4983230072969 + 3 ^ 40 * 970873 * 2
def baseEnd_970873 : Nat := 221566445987860083832241

theorem tailTrace_970873 : CollatzResearch.WordTrace tailWord_970873 prefixEnd_970873 221566445987860083832241 := by
  unfold tailWord_970873
  simp only [CollatzResearch.WordTrace]
  refine ⟨35410647411700407752549273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23607098274466938501699515 35410647411700407752549273)
  ·
    refine ⟨26557985558775305814411955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35410647411700407752549273 26557985558775305814411955)
    ·
      refine ⟨39836978338162958721617933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26557985558775305814411955 39836978338162958721617933)
      ·
        refine ⟨14938866876811109520606725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39836978338162958721617933 14938866876811109520606725)
        ·
          refine ⟨2801037539402083035113761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14938866876811109520606725 2801037539402083035113761)
          ·
            refine ⟨2100778154551562276335321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2801037539402083035113761 2100778154551562276335321)
            ·
              refine ⟨1575583615913671707251491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2100778154551562276335321 1575583615913671707251491)
              ·
                refine ⟨2363375423870507560877237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1575583615913671707251491 2363375423870507560877237)
                ·
                  refine ⟨221566445987860083832241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2363375423870507560877237 221566445987860083832241)
                  ·
                    rfl

theorem cell21_970873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 5].length) (baseStart_970873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_970873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_970873 prefixEnd_970873 := by exact prefixLift 970873
  have htrace : WordTrace (prefixWord ++ tailWord_970873) baseStart_970873 baseEnd_970873 := by
    simpa [prefixWord, tailWord_970873, baseEnd_970873] using wordTrace_append hprefix tailTrace_970873
  have hstable : (prefixWord ++ tailWord_970873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970873).length < 2 ^ (prefixWord ++ tailWord_970873).sum := by decide
  have hdescent : baseEnd_970873 < baseStart_970873 := by decide
  rcases family_descends (prefixWord ++ tailWord_970873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970887 : List Nat := [1, 1, 4, 2, 1, 1, 2, 5, 4]
def baseStart_970887 : Nat := 118140960795 + 970887 * 2 ^ 59
def prefixEnd_970887 : Nat := 4983230072969 + 3 ^ 40 * 970887 * 2
def baseEnd_970887 : Nat := 221569640978599170598879

theorem tailTrace_970887 : CollatzResearch.WordTrace tailWord_970887 prefixEnd_970887 221569640978599170598879 := by
  unfold tailWord_970887
  simp only [CollatzResearch.WordTrace]
  refine ⟨35411158033649688143558915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23607438689099792095705943 35411158033649688143558915)
  ·
    refine ⟨53116737050474532215338373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35411158033649688143558915 53116737050474532215338373)
    ·
      refine ⟨9959388196963974790375945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53116737050474532215338373 9959388196963974790375945)
      ·
        refine ⟨7469541147722981092781959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9959388196963974790375945 7469541147722981092781959)
        ·
          refine ⟨11204311721584471639172939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7469541147722981092781959 11204311721584471639172939)
          ·
            refine ⟨16806467582376707458759409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11204311721584471639172939 16806467582376707458759409)
            ·
              refine ⟨12604850686782530594069557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16806467582376707458759409 12604850686782530594069557)
              ·
                refine ⟨1181704751885862243194021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12604850686782530594069557 1181704751885862243194021)
                ·
                  refine ⟨221569640978599170598879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1181704751885862243194021 221569640978599170598879)
                  ·
                    rfl

theorem cell21_970887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5, 4].length) (baseStart_970887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_970887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_970887 prefixEnd_970887 := by exact prefixLift 970887
  have htrace : WordTrace (prefixWord ++ tailWord_970887) baseStart_970887 baseEnd_970887 := by
    simpa [prefixWord, tailWord_970887, baseEnd_970887] using wordTrace_append hprefix tailTrace_970887
  have hstable : (prefixWord ++ tailWord_970887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970887).length < 2 ^ (prefixWord ++ tailWord_970887).sum := by decide
  have hdescent : baseEnd_970887 < baseStart_970887 := by decide
  rcases family_descends (prefixWord ++ tailWord_970887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970901 : List Nat := [1, 3, 2, 1, 1, 1, 5, 7]
def baseStart_970901 : Nat := 118140960795 + 970901 * 2 ^ 59
def prefixEnd_970901 : Nat := 4983230072969 + 3 ^ 40 * 970901 * 2
def baseEnd_970901 : Nat := 73857611989779419121839

theorem tailTrace_970901 : CollatzResearch.WordTrace tailWord_970901 prefixEnd_970901 73857611989779419121839 := by
  unfold tailWord_970901
  simp only [CollatzResearch.WordTrace]
  refine ⟨35411668655598968534568557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23607779103732645689712371 35411668655598968534568557)
  ·
    refine ⟨13279375745849613200463209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35411668655598968534568557 13279375745849613200463209)
    ·
      refine ⟨9959531809387209900347407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13279375745849613200463209 9959531809387209900347407)
      ·
        refine ⟨14939297714080814850521111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9959531809387209900347407 14939297714080814850521111)
        ·
          refine ⟨22408946571121222275781667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14939297714080814850521111 22408946571121222275781667)
          ·
            refine ⟨33613419856681833413672501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22408946571121222275781667 33613419856681833413672501)
            ·
              refine ⟨3151258111563921882531797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33613419856681833413672501 3151258111563921882531797)
              ·
                refine ⟨73857611989779419121839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3151258111563921882531797 73857611989779419121839)
                ·
                  rfl

theorem cell21_970901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 7].length) (baseStart_970901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_970901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_970901 prefixEnd_970901 := by exact prefixLift 970901
  have htrace : WordTrace (prefixWord ++ tailWord_970901) baseStart_970901 baseEnd_970901 := by
    simpa [prefixWord, tailWord_970901, baseEnd_970901] using wordTrace_append hprefix tailTrace_970901
  have hstable : (prefixWord ++ tailWord_970901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970901).length < 2 ^ (prefixWord ++ tailWord_970901).sum := by decide
  have hdescent : baseEnd_970901 < baseStart_970901 := by decide
  rcases family_descends (prefixWord ++ tailWord_970901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970983 : List Nat := [1, 1, 5, 3, 1, 1, 4, 2, 3]
def baseStart_970983 : Nat := 118140960795 + 970983 * 2 ^ 59
def prefixEnd_970983 : Nat := 4983230072969 + 3 ^ 40 * 970983 * 2
def baseEnd_970983 : Nat := 221591549486524336998683

theorem tailTrace_970983 : CollatzResearch.WordTrace tailWord_970983 prefixEnd_970983 221591549486524336998683 := by
  unfold tailWord_970983
  simp only [CollatzResearch.WordTrace]
  refine ⟨35414659441301896539053603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23609772960867931026035735 35414659441301896539053603)
  ·
    refine ⟨53121989161952844808580405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35414659441301896539053603 53121989161952844808580405)
    ·
      refine ⟨4980186483933079200804413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53121989161952844808580405 4980186483933079200804413)
      ·
        refine ⟨1867569931474904700301655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4980186483933079200804413 1867569931474904700301655)
        ·
          refine ⟨2801354897212357050452483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1867569931474904700301655 2801354897212357050452483)
          ·
            refine ⟨4202032345818535575678725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2801354897212357050452483 4202032345818535575678725)
            ·
              refine ⟨787881064840975420439761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4202032345818535575678725 787881064840975420439761)
              ·
                refine ⟨590910798630731565329821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 787881064840975420439761 590910798630731565329821)
                ·
                  refine ⟨221591549486524336998683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 590910798630731565329821 221591549486524336998683)
                  ·
                    rfl

theorem cell21_970983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 2, 3].length) (baseStart_970983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_970983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_970983 prefixEnd_970983 := by exact prefixLift 970983
  have htrace : WordTrace (prefixWord ++ tailWord_970983) baseStart_970983 baseEnd_970983 := by
    simpa [prefixWord, tailWord_970983, baseEnd_970983] using wordTrace_append hprefix tailTrace_970983
  have hstable : (prefixWord ++ tailWord_970983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970983).length < 2 ^ (prefixWord ++ tailWord_970983).sum := by decide
  have hdescent : baseEnd_970983 < baseStart_970983 := by decide
  rcases family_descends (prefixWord ++ tailWord_970983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_970994 : List Nat := [3, 2, 1, 3, 2, 1, 3, 6]
def baseStart_970994 : Nat := 118140960795 + 970994 * 2 ^ 59
def prefixEnd_970994 : Nat := 4983230072969 + 3 ^ 40 * 970994 * 2
def baseEnd_970994 : Nat := 73864686612130254105109

theorem tailTrace_970994 : CollatzResearch.WordTrace tailWord_970994 prefixEnd_970994 73864686612130254105109 := by
  unfold tailWord_970994
  simp only [CollatzResearch.WordTrace]
  refine ⟨8853765161065511354426009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23610040429508030278469357 8853765161065511354426009)
  ·
    refine ⟨6640323870799133515819507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8853765161065511354426009 6640323870799133515819507)
    ·
      refine ⟨9960485806198700273729261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6640323870799133515819507 9960485806198700273729261)
      ·
        refine ⟨3735182177324512602648473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9960485806198700273729261 3735182177324512602648473)
        ·
          refine ⟨2801386632993384451986355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3735182177324512602648473 2801386632993384451986355)
          ·
            refine ⟨4202079949490076677979533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2801386632993384451986355 4202079949490076677979533)
            ·
              refine ⟨1575779981058778754242325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4202079949490076677979533 1575779981058778754242325)
              ·
                refine ⟨73864686612130254105109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1575779981058778754242325 73864686612130254105109)
                ·
                  rfl

theorem cell21_970994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 6].length) (baseStart_970994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_970994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_970994 prefixEnd_970994 := by exact prefixLift 970994
  have htrace : WordTrace (prefixWord ++ tailWord_970994) baseStart_970994 baseEnd_970994 := by
    simpa [prefixWord, tailWord_970994, baseEnd_970994] using wordTrace_append hprefix tailTrace_970994
  have hstable : (prefixWord ++ tailWord_970994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_970994).length < 2 ^ (prefixWord ++ tailWord_970994).sum := by decide
  have hdescent : baseEnd_970994 < baseStart_970994 := by decide
  rcases family_descends (prefixWord ++ tailWord_970994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971025 : List Nat := [1, 2, 2, 1, 1, 5, 1, 5, 3]
def baseStart_971025 : Nat := 118140960795 + 971025 * 2 ^ 59
def prefixEnd_971025 : Nat := 4983230072969 + 3 ^ 40 * 971025 * 2
def baseEnd_971025 : Nat := 221601134458741597298597

theorem tailTrace_971025 : CollatzResearch.WordTrace tailWord_971025 prefixEnd_971025 221601134458741597298597 := by
  unfold tailWord_971025
  simp only [CollatzResearch.WordTrace]
  refine ⟨35416191307149737712082529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23610794204766491808055019 35416191307149737712082529)
  ·
    refine ⟨26562143480362303284061897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35416191307149737712082529 26562143480362303284061897)
    ·
      refine ⟨19921607610271727463046423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26562143480362303284061897 19921607610271727463046423)
      ·
        refine ⟨29882411415407591194569635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19921607610271727463046423 29882411415407591194569635)
        ·
          refine ⟨44823617123111386791854453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29882411415407591194569635 44823617123111386791854453)
          ·
            refine ⟨4202214105291692511736355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44823617123111386791854453 4202214105291692511736355)
            ·
              refine ⟨6303321157937538767604533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4202214105291692511736355 6303321157937538767604533)
              ·
                refine ⟨590936358556644259462925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6303321157937538767604533 590936358556644259462925)
                ·
                  refine ⟨221601134458741597298597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 590936358556644259462925 221601134458741597298597)
                  ·
                    rfl

theorem cell21_971025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 5, 3].length) (baseStart_971025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_971025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_971025 prefixEnd_971025 := by exact prefixLift 971025
  have htrace : WordTrace (prefixWord ++ tailWord_971025) baseStart_971025 baseEnd_971025 := by
    simpa [prefixWord, tailWord_971025, baseEnd_971025] using wordTrace_append hprefix tailTrace_971025
  have hstable : (prefixWord ++ tailWord_971025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971025).length < 2 ^ (prefixWord ++ tailWord_971025).sum := by decide
  have hdescent : baseEnd_971025 < baseStart_971025 := by decide
  rcases family_descends (prefixWord ++ tailWord_971025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971039 : List Nat := [1, 1, 2, 4, 3, 2, 1, 1, 6]
def baseStart_971039 : Nat := 118140960795 + 971039 * 2 ^ 59
def prefixEnd_971039 : Nat := 4983230072969 + 3 ^ 40 * 971039 * 2
def baseEnd_971039 : Nat := 221604329449480684065235

theorem tailTrace_971039 : CollatzResearch.WordTrace tailWord_971039 prefixEnd_971039 221604329449480684065235 := by
  unfold tailWord_971039
  simp only [CollatzResearch.WordTrace]
  refine ⟨35416701929099018103092171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23611134619399345402061447 35416701929099018103092171)
  ·
    refine ⟨53125052893648527154638257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35416701929099018103092171 53125052893648527154638257)
    ·
      refine ⟨39843789670236395365978693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53125052893648527154638257 39843789670236395365978693)
      ·
        refine ⟨7470710563169324131121005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39843789670236395365978693 7470710563169324131121005)
        ·
          refine ⟨2801516461188496549170377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7470710563169324131121005 2801516461188496549170377)
          ·
            refine ⟨2101137345891372411877783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2801516461188496549170377 2101137345891372411877783)
            ·
              refine ⟨3151706018837058617816675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2101137345891372411877783 3151706018837058617816675)
              ·
                refine ⟨4727559028255587926725013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3151706018837058617816675 4727559028255587926725013)
                ·
                  refine ⟨221604329449480684065235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4727559028255587926725013 221604329449480684065235)
                  ·
                    rfl

theorem cell21_971039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 6].length) (baseStart_971039 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_971039 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_971039 prefixEnd_971039 := by exact prefixLift 971039
  have htrace : WordTrace (prefixWord ++ tailWord_971039) baseStart_971039 baseEnd_971039 := by
    simpa [prefixWord, tailWord_971039, baseEnd_971039] using wordTrace_append hprefix tailTrace_971039
  have hstable : (prefixWord ++ tailWord_971039).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971039).length < 2 ^ (prefixWord ++ tailWord_971039).sum := by decide
  have hdescent : baseEnd_971039 < baseStart_971039 := by decide
  rcases family_descends (prefixWord ++ tailWord_971039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971042 : List Nat := [3, 3, 1, 1, 3, 1, 2, 4, 3]
def baseStart_971042 : Nat := 118140960795 + 971042 * 2 ^ 59
def prefixEnd_971042 : Nat := 4983230072969 + 3 ^ 40 * 971042 * 2
def baseEnd_971042 : Nat := 221605014090353345515229

theorem tailTrace_971042 : CollatzResearch.WordTrace tailWord_971042 prefixEnd_971042 221605014090353345515229 := by
  unfold tailWord_971042
  simp only [CollatzResearch.WordTrace]
  refine ⟨8854202837022037403862845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23611207565392099743634253 8854202837022037403862845)
  ·
    refine ⟨3320326063883264026448567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8854202837022037403862845 3320326063883264026448567)
    ·
      refine ⟨4980489095824896039672851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3320326063883264026448567 4980489095824896039672851)
      ·
        refine ⟨7470733643737344059509277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4980489095824896039672851 7470733643737344059509277)
        ·
          refine ⟨2801525116401504022315979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7470733643737344059509277 2801525116401504022315979)
          ·
            refine ⟨4202287674602256033473969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2801525116401504022315979 4202287674602256033473969)
            ·
              refine ⟨3151715755951692025105477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4202287674602256033473969 3151715755951692025105477)
              ·
                refine ⟨590946704240942254707277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3151715755951692025105477 590946704240942254707277)
                ·
                  refine ⟨221605014090353345515229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 590946704240942254707277 221605014090353345515229)
                  ·
                    rfl

theorem cell21_971042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_971042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_971042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_971042 prefixEnd_971042 := by exact prefixLift 971042
  have htrace : WordTrace (prefixWord ++ tailWord_971042) baseStart_971042 baseEnd_971042 := by
    simpa [prefixWord, tailWord_971042, baseEnd_971042] using wordTrace_append hprefix tailTrace_971042
  have hstable : (prefixWord ++ tailWord_971042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971042).length < 2 ^ (prefixWord ++ tailWord_971042).sum := by decide
  have hdescent : baseEnd_971042 < baseStart_971042 := by decide
  rcases family_descends (prefixWord ++ tailWord_971042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971070 : List Nat := [4, 2, 1, 2, 1, 3, 1, 7]
def baseStart_971070 : Nat := 118140960795 + 971070 * 2 ^ 59
def prefixEnd_971070 : Nat := 4983230072969 + 3 ^ 40 * 971070 * 2
def baseEnd_971070 : Nat := 73870468023943839682835

theorem tailTrace_971070 : CollatzResearch.WordTrace tailWord_971070 prefixEnd_971070 73870468023943839682835 := by
  unfold tailWord_971070
  simp only [CollatzResearch.WordTrace]
  refine ⟨4427229073998338799683833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23611888394657806931647109 4427229073998338799683833)
  ·
    refine ⟨3320421805498754099762875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4427229073998338799683833 3320421805498754099762875)
    ·
      refine ⟨4980632708248131149644313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3320421805498754099762875 4980632708248131149644313)
      ·
        refine ⟨3735474531186098362233235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4980632708248131149644313 3735474531186098362233235)
        ·
          refine ⟨5603211796779147543349853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3735474531186098362233235 5603211796779147543349853)
          ·
            refine ⟨2101204423792180328756195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5603211796779147543349853 2101204423792180328756195)
            ·
              refine ⟨3151806635688270493134293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2101204423792180328756195 3151806635688270493134293)
              ·
                refine ⟨73870468023943839682835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3151806635688270493134293 73870468023943839682835)
                ·
                  rfl

theorem cell21_971070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_971070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_971070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_971070 prefixEnd_971070 := by exact prefixLift 971070
  have htrace : WordTrace (prefixWord ++ tailWord_971070) baseStart_971070 baseEnd_971070 := by
    simpa [prefixWord, tailWord_971070, baseEnd_971070] using wordTrace_append hprefix tailTrace_971070
  have hstable : (prefixWord ++ tailWord_971070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971070).length < 2 ^ (prefixWord ++ tailWord_971070).sum := by decide
  have hdescent : baseEnd_971070 < baseStart_971070 := by decide
  rcases family_descends (prefixWord ++ tailWord_971070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971076 : List Nat := [2, 3, 4, 1, 2, 2, 1, 3, 3]
def baseStart_971076 : Nat := 118140960795 + 971076 * 2 ^ 59
def prefixEnd_971076 : Nat := 4983230072969 + 3 ^ 40 * 971076 * 2
def baseEnd_971076 : Nat := 221612773353576841948493

theorem tailTrace_971076 : CollatzResearch.WordTrace tailWord_971076 prefixEnd_971076 221612773353576841948493 := by
  unfold tailWord_971076
  simp only [CollatzResearch.WordTrace]
  refine ⟨17709025714982486711094541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23612034286643315614792721 17709025714982486711094541)
  ·
    refine ⟨6640884643118432516660453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17709025714982486711094541 6640884643118432516660453)
    ·
      refine ⟨1245165870584706096873835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6640884643118432516660453 1245165870584706096873835)
      ·
        refine ⟨1867748805877059145310753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1245165870584706096873835 1867748805877059145310753)
        ·
          refine ⟨1400811604407794358983065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1867748805877059145310753 1400811604407794358983065)
          ·
            refine ⟨1050608703305845769237299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1400811604407794358983065 1050608703305845769237299)
            ·
              refine ⟨1575913054958768653855949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1050608703305845769237299 1575913054958768653855949)
              ·
                refine ⟨590967395609538245195981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1575913054958768653855949 590967395609538245195981)
                ·
                  refine ⟨221612773353576841948493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 590967395609538245195981 221612773353576841948493)
                  ·
                    rfl

theorem cell21_971076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 3, 3].length) (baseStart_971076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_971076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_971076 prefixEnd_971076 := by exact prefixLift 971076
  have htrace : WordTrace (prefixWord ++ tailWord_971076) baseStart_971076 baseEnd_971076 := by
    simpa [prefixWord, tailWord_971076, baseEnd_971076] using wordTrace_append hprefix tailTrace_971076
  have hstable : (prefixWord ++ tailWord_971076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971076).length < 2 ^ (prefixWord ++ tailWord_971076).sum := by decide
  have hdescent : baseEnd_971076 < baseStart_971076 := by decide
  rcases family_descends (prefixWord ++ tailWord_971076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971146 : List Nat := [3, 1, 2, 5, 1, 9]
def baseStart_971146 : Nat := 118140960795 + 971146 * 2 ^ 59
def prefixEnd_971146 : Nat := 4983230072969 + 3 ^ 40 * 971146 * 2
def baseEnd_971146 : Nat := 8208472159528602806729

theorem tailTrace_971146 : CollatzResearch.WordTrace tailWord_971146 prefixEnd_971146 8208472159528602806729 := by
  unfold tailWord_971146
  simp only [CollatzResearch.WordTrace]
  refine ⟨8855151134927843844309323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23613736359807583584824861 8855151134927843844309323)
  ·
    refine ⟨13282726702391765766463985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8855151134927843844309323 13282726702391765766463985)
    ·
      refine ⟨9962045026793824324847989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13282726702391765766463985 9962045026793824324847989)
      ·
        refine ⟨933941721261921030454499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9962045026793824324847989 933941721261921030454499)
        ·
          refine ⟨1400912581892881545681749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 933941721261921030454499 1400912581892881545681749)
          ·
            refine ⟨8208472159528602806729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1400912581892881545681749 8208472159528602806729)
            ·
              rfl

theorem cell21_971146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 9].length) (baseStart_971146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_971146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_971146 prefixEnd_971146 := by exact prefixLift 971146
  have htrace : WordTrace (prefixWord ++ tailWord_971146) baseStart_971146 baseEnd_971146 := by
    simpa [prefixWord, tailWord_971146, baseEnd_971146] using wordTrace_append hprefix tailTrace_971146
  have hstable : (prefixWord ++ tailWord_971146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971146).length < 2 ^ (prefixWord ++ tailWord_971146).sum := by decide
  have hdescent : baseEnd_971146 < baseStart_971146 := by decide
  rcases family_descends (prefixWord ++ tailWord_971146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971208 : List Nat := [2, 1, 3, 1, 3, 4, 1, 2, 4]
def baseStart_971208 : Nat := 118140960795 + 971208 * 2 ^ 59
def prefixEnd_971208 : Nat := 4983230072969 + 3 ^ 40 * 971208 * 2
def baseEnd_971208 : Nat := 221642897551973945748223

theorem tailTrace_971208 : CollatzResearch.WordTrace tailWord_971208 prefixEnd_971208 221642897551973945748223 := by
  unfold tailWord_971208
  simp only [CollatzResearch.WordTrace]
  refine ⟨17711432932743379982997139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23615243910324506643996185 17711432932743379982997139)
  ·
    refine ⟨26567149399115069974495709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17711432932743379982997139 26567149399115069974495709)
    ·
      refine ⟨9962681024668151240435891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26567149399115069974495709 9962681024668151240435891)
      ·
        refine ⟨14944021537002226860653837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9962681024668151240435891 14944021537002226860653837)
        ·
          refine ⟨5604008076375835072745189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14944021537002226860653837 5604008076375835072745189)
          ·
            refine ⟨1050751514320469076139723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5604008076375835072745189 1050751514320469076139723)
            ·
              refine ⟨1576127271480703614209585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1050751514320469076139723 1576127271480703614209585)
              ·
                refine ⟨1182095453610527710657189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1576127271480703614209585 1182095453610527710657189)
                ·
                  refine ⟨221642897551973945748223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1182095453610527710657189 221642897551973945748223)
                  ·
                    rfl

theorem cell21_971208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 2, 4].length) (baseStart_971208 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_971208 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_971208 prefixEnd_971208 := by exact prefixLift 971208
  have htrace : WordTrace (prefixWord ++ tailWord_971208) baseStart_971208 baseEnd_971208 := by
    simpa [prefixWord, tailWord_971208, baseEnd_971208] using wordTrace_append hprefix tailTrace_971208
  have hstable : (prefixWord ++ tailWord_971208).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971208).length < 2 ^ (prefixWord ++ tailWord_971208).sum := by decide
  have hdescent : baseEnd_971208 < baseStart_971208 := by decide
  rcases family_descends (prefixWord ++ tailWord_971208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971222 : List Nat := [5, 2, 1, 1, 1, 1, 2, 8]
def baseStart_971222 : Nat := 118140960795 + 971222 * 2 ^ 59
def prefixEnd_971222 : Nat := 4983230072969 + 3 ^ 40 * 971222 * 2
def baseEnd_971222 : Nat := 73882030847571010838287

theorem tailTrace_971222 : CollatzResearch.WordTrace tailWord_971222 prefixEnd_971222 73882030847571010838287 := by
  unfold tailWord_971222
  simp only [CollatzResearch.WordTrace]
  refine ⟨2213961030464752522312745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23615584324957360238002613 2213961030464752522312745)
  ·
    refine ⟨1660470772848564391734559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2213961030464752522312745 1660470772848564391734559)
    ·
      refine ⟨2490706159272846587601839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1660470772848564391734559 2490706159272846587601839)
      ·
        refine ⟨3736059238909269881402759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2490706159272846587601839 3736059238909269881402759)
        ·
          refine ⟨5604088858363904822104139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3736059238909269881402759 5604088858363904822104139)
          ·
            refine ⟨8406133287545857233156209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5604088858363904822104139 8406133287545857233156209)
            ·
              refine ⟨6304599965659392924867157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8406133287545857233156209 6304599965659392924867157)
              ·
                refine ⟨73882030847571010838287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6304599965659392924867157 73882030847571010838287)
                ·
                  rfl

theorem cell21_971222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_971222 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_971222 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_971222 prefixEnd_971222 := by exact prefixLift 971222
  have htrace : WordTrace (prefixWord ++ tailWord_971222) baseStart_971222 baseEnd_971222 := by
    simpa [prefixWord, tailWord_971222, baseEnd_971222] using wordTrace_append hprefix tailTrace_971222
  have hstable : (prefixWord ++ tailWord_971222).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971222).length < 2 ^ (prefixWord ++ tailWord_971222).sum := by decide
  have hdescent : baseEnd_971222 < baseStart_971222 := by decide
  rcases family_descends (prefixWord ++ tailWord_971222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971295 : List Nat := [1, 1, 2, 4, 1, 1, 1, 3, 7]
def baseStart_971295 : Nat := 118140960795 + 971295 * 2 ^ 59
def prefixEnd_971295 : Nat := 4983230072969 + 3 ^ 40 * 971295 * 2
def baseEnd_971295 : Nat := 221662752137281127798045

theorem tailTrace_971295 : CollatzResearch.WordTrace tailWord_971295 prefixEnd_971295 221662752137281127798045 := by
  unfold tailWord_971295
  simp only [CollatzResearch.WordTrace]
  refine ⟨35426039016171573824411339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23617359344114382549607559 35426039016171573824411339)
  ·
    refine ⟨53139058524257360736617009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35426039016171573824411339 53139058524257360736617009)
    ·
      refine ⟨39854293893193020552462757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53139058524257360736617009 39854293893193020552462757)
      ·
        refine ⟨7472680104973691353586767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39854293893193020552462757 7472680104973691353586767)
        ·
          refine ⟨11209020157460537030380151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7472680104973691353586767 11209020157460537030380151)
          ·
            refine ⟨16813530236190805545570227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11209020157460537030380151 16813530236190805545570227)
            ·
              refine ⟨25220295354286208318355341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16813530236190805545570227 25220295354286208318355341)
              ·
                refine ⟨9457610757857328119383253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25220295354286208318355341 9457610757857328119383253)
                ·
                  refine ⟨221662752137281127798045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9457610757857328119383253 221662752137281127798045)
                  ·
                    rfl

theorem cell21_971295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 7].length) (baseStart_971295 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_971295 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_971295 prefixEnd_971295 := by exact prefixLift 971295
  have htrace : WordTrace (prefixWord ++ tailWord_971295) baseStart_971295 baseEnd_971295 := by
    simpa [prefixWord, tailWord_971295, baseEnd_971295] using wordTrace_append hprefix tailTrace_971295
  have hstable : (prefixWord ++ tailWord_971295).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971295).length < 2 ^ (prefixWord ++ tailWord_971295).sum := by decide
  have hdescent : baseEnd_971295 < baseStart_971295 := by decide
  rcases family_descends (prefixWord ++ tailWord_971295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971492 : List Nat := [2, 3, 1, 1, 1, 13]
def baseStart_971492 : Nat := 118140960795 + 971492 * 2 ^ 59
def prefixEnd_971492 : Nat := 4983230072969 + 3 ^ 40 * 971492 * 2
def baseEnd_971492 : Nat := 8211396674861206037567

theorem tailTrace_971492 : CollatzResearch.WordTrace tailWord_971492 prefixEnd_971492 8211396674861206037567 := by
  unfold tailWord_971492
  simp only [CollatzResearch.WordTrace]
  refine ⟨17716612098228938234666365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23622149464305250979555153 17716612098228938234666365)
  ·
    refine ⟨6643729536835851837999887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17716612098228938234666365 6643729536835851837999887)
    ·
      refine ⟨9965594305253777756999831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6643729536835851837999887 9965594305253777756999831)
      ·
        refine ⟨14948391457880666635499747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9965594305253777756999831 14948391457880666635499747)
        ·
          refine ⟨22422587186820999953249621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14948391457880666635499747 22422587186820999953249621)
          ·
            refine ⟨8211396674861206037567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 22422587186820999953249621 8211396674861206037567)
            ·
              rfl

theorem cell21_971492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 13].length) (baseStart_971492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_971492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_971492 prefixEnd_971492 := by exact prefixLift 971492
  have htrace : WordTrace (prefixWord ++ tailWord_971492) baseStart_971492 baseEnd_971492 := by
    simpa [prefixWord, tailWord_971492, baseEnd_971492] using wordTrace_append hprefix tailTrace_971492
  have hstable : (prefixWord ++ tailWord_971492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971492).length < 2 ^ (prefixWord ++ tailWord_971492).sum := by decide
  have hdescent : baseEnd_971492 < baseStart_971492 := by decide
  rcases family_descends (prefixWord ++ tailWord_971492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971723 : List Nat := [1, 1, 1, 1, 3, 7, 1, 2, 4]
def baseStart_971723 : Nat := 118140960795 + 971723 * 2 ^ 59
def prefixEnd_971723 : Nat := 4983230072969 + 3 ^ 40 * 971723 * 2
def baseEnd_971723 : Nat := 221760427568447494663837

theorem tailTrace_971723 : CollatzResearch.WordTrace tailWord_971723 prefixEnd_971723 221760427568447494663837 := by
  unfold tailWord_971723
  simp only [CollatzResearch.WordTrace]
  refine ⟨35441649458621002920991823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23627766305747335280661215 35441649458621002920991823)
  ·
    refine ⟨53162474187931504381487735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35441649458621002920991823 53162474187931504381487735)
    ·
      refine ⟨79743711281897256572231603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53162474187931504381487735 79743711281897256572231603)
      ·
        refine ⟨119615566922845884858347405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79743711281897256572231603 119615566922845884858347405)
        ·
          refine ⟨44855837596067206821880277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119615566922845884858347405 44855837596067206821880277)
          ·
            refine ⟨1051308693657825159887819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 44855837596067206821880277 1051308693657825159887819)
            ·
              refine ⟨1576963040486737739831729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1051308693657825159887819 1576963040486737739831729)
              ·
                refine ⟨1182722280365053304873797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1576963040486737739831729 1182722280365053304873797)
                ·
                  refine ⟨221760427568447494663837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1182722280365053304873797 221760427568447494663837)
                  ·
                    rfl

theorem cell21_971723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 2, 4].length) (baseStart_971723 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_971723 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_971723 prefixEnd_971723 := by exact prefixLift 971723
  have htrace : WordTrace (prefixWord ++ tailWord_971723) baseStart_971723 baseEnd_971723 := by
    simpa [prefixWord, tailWord_971723, baseEnd_971723] using wordTrace_append hprefix tailTrace_971723
  have hstable : (prefixWord ++ tailWord_971723).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971723).length < 2 ^ (prefixWord ++ tailWord_971723).sum := by decide
  have hdescent : baseEnd_971723 < baseStart_971723 := by decide
  rcases family_descends (prefixWord ++ tailWord_971723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971754 : List Nat := [3, 1, 3, 1, 2, 4, 2, 5]
def baseStart_971754 : Nat := 118140960795 + 971754 * 2 ^ 59
def prefixEnd_971754 : Nat := 4983230072969 + 3 ^ 40 * 971754 * 2
def baseEnd_971754 : Nat := 73922500730266109882369

theorem tailTrace_971754 : CollatzResearch.WordTrace tailWord_971754 prefixEnd_971754 73922500730266109882369 := by
  unfold tailWord_971754
  simp only [CollatzResearch.WordTrace]
  refine ⟨8860695030377173803842579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23628520081005796810246877 8860695030377173803842579)
  ·
    refine ⟨13291042545565760705763869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8860695030377173803842579 13291042545565760705763869)
    ·
      refine ⟨4984140954587160264661451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13291042545565760705763869 4984140954587160264661451)
      ·
        refine ⟨7476211431880740396992177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4984140954587160264661451 7476211431880740396992177)
        ·
          refine ⟨5607158573910555297744133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7476211431880740396992177 5607158573910555297744133)
          ·
            refine ⟨1051342232608229118327025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5607158573910555297744133 1051342232608229118327025)
            ·
              refine ⟨788506674456171838745269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1051342232608229118327025 788506674456171838745269)
              ·
                refine ⟨73922500730266109882369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 788506674456171838745269 73922500730266109882369)
                ·
                  rfl

theorem cell21_971754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 5].length) (baseStart_971754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_971754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_971754 prefixEnd_971754 := by exact prefixLift 971754
  have htrace : WordTrace (prefixWord ++ tailWord_971754) baseStart_971754 baseEnd_971754 := by
    simpa [prefixWord, tailWord_971754, baseEnd_971754] using wordTrace_append hprefix tailTrace_971754
  have hstable : (prefixWord ++ tailWord_971754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971754).length < 2 ^ (prefixWord ++ tailWord_971754).sum := by decide
  have hdescent : baseEnd_971754 < baseStart_971754 := by decide
  rcases family_descends (prefixWord ++ tailWord_971754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971799 : List Nat := [1, 1, 3, 5, 1, 2, 1, 3, 4]
def baseStart_971799 : Nat := 118140960795 + 971799 * 2 ^ 59
def prefixEnd_971799 : Nat := 4983230072969 + 3 ^ 40 * 971799 * 2
def baseEnd_971799 : Nat := 221777771803888251397015

theorem tailTrace_971799 : CollatzResearch.WordTrace tailWord_971799 prefixEnd_971799 221777771803888251397015 := by
  unfold tailWord_971799
  simp only [CollatzResearch.WordTrace]
  refine ⟨35444421406345667900758451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23629614270897111933838967 35444421406345667900758451)
  ·
    refine ⟨53166632109518501851137677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35444421406345667900758451 53166632109518501851137677)
    ·
      refine ⟨19937487041069438194176629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53166632109518501851137677 19937487041069438194176629)
      ·
        refine ⟨1869139410100259830704059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19937487041069438194176629 1869139410100259830704059)
        ·
          refine ⟨2803709115150389746056089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1869139410100259830704059 2803709115150389746056089)
          ·
            refine ⟨2102781836362792309542067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2803709115150389746056089 2102781836362792309542067)
            ·
              refine ⟨3154172754544188464313101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2102781836362792309542067 3154172754544188464313101)
              ·
                refine ⟨1182814782954070674117413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3154172754544188464313101 1182814782954070674117413)
                ·
                  refine ⟨221777771803888251397015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1182814782954070674117413 221777771803888251397015)
                  ·
                    rfl

theorem cell21_971799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3, 4].length) (baseStart_971799 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_971799 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_971799 prefixEnd_971799 := by exact prefixLift 971799
  have htrace : WordTrace (prefixWord ++ tailWord_971799) baseStart_971799 baseEnd_971799 := by
    simpa [prefixWord, tailWord_971799, baseEnd_971799] using wordTrace_append hprefix tailTrace_971799
  have hstable : (prefixWord ++ tailWord_971799).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971799).length < 2 ^ (prefixWord ++ tailWord_971799).sum := by decide
  have hdescent : baseEnd_971799 < baseStart_971799 := by decide
  rcases family_descends (prefixWord ++ tailWord_971799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_971968 : List Nat := [2, 1, 1, 2, 6, 2, 2, 1, 4]
def baseStart_971968 : Nat := 118140960795 + 971968 * 2 ^ 59
def prefixEnd_971968 : Nat := 4983230072969 + 3 ^ 40 * 971968 * 2
def baseEnd_971968 : Nat := 221816339906381513080003

theorem tailTrace_971968 : CollatzResearch.WordTrace tailWord_971968 prefixEnd_971968 221816339906381513080003 := by
  unfold tailWord_971968
  simp only [CollatzResearch.WordTrace]
  refine ⟨17725292671366704881830279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23633723561822273175773705 17725292671366704881830279)
  ·
    refine ⟨26587939007050057322745419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17725292671366704881830279 26587939007050057322745419)
    ·
      refine ⟨39881908510575085984118129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26587939007050057322745419 39881908510575085984118129)
      ·
        refine ⟨29911431382931314488088597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39881908510575085984118129 29911431382931314488088597)
        ·
          refine ⟨1402098346074905366629153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29911431382931314488088597 1402098346074905366629153)
          ·
            refine ⟨1051573759556179024971865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1402098346074905366629153 1051573759556179024971865)
            ·
              refine ⟨788680319667134268728899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1051573759556179024971865 788680319667134268728899)
              ·
                refine ⟨1183020479500701403093349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 788680319667134268728899 1183020479500701403093349)
                ·
                  refine ⟨221816339906381513080003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1183020479500701403093349 221816339906381513080003)
                  ·
                    rfl

theorem cell21_971968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 1, 4].length) (baseStart_971968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_971968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_971968 prefixEnd_971968 := by exact prefixLift 971968
  have htrace : WordTrace (prefixWord ++ tailWord_971968) baseStart_971968 baseEnd_971968 := by
    simpa [prefixWord, tailWord_971968, baseEnd_971968] using wordTrace_append hprefix tailTrace_971968
  have hstable : (prefixWord ++ tailWord_971968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_971968).length < 2 ^ (prefixWord ++ tailWord_971968).sum := by decide
  have hdescent : baseEnd_971968 < baseStart_971968 := by decide
  rcases family_descends (prefixWord ++ tailWord_971968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972010 : List Nat := [3, 1, 3, 1, 1, 3, 1, 4, 4]
def baseStart_972010 : Nat := 118140960795 + 972010 * 2 ^ 59
def prefixEnd_972010 : Nat := 4983230072969 + 3 ^ 40 * 972010 * 2
def baseEnd_972010 : Nat := 221825924878598773379917

theorem tailTrace_972010 : CollatzResearch.WordTrace tailWord_972010 prefixEnd_972010 221825924878598773379917 := by
  unfold tailWord_972010
  simp only [CollatzResearch.WordTrace]
  refine ⟨8863029302145312734172371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23634744805720833957792989 8863029302145312734172371)
  ·
    refine ⟨13294543953217969101258557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8863029302145312734172371 13294543953217969101258557)
    ·
      refine ⟨4985453982456738412971959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13294543953217969101258557 4985453982456738412971959)
      ·
        refine ⟨7478180973685107619457939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4985453982456738412971959 7478180973685107619457939)
        ·
          refine ⟨11217271460527661429186909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7478180973685107619457939 11217271460527661429186909)
          ·
            refine ⟨4206476797697873035945091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11217271460527661429186909 4206476797697873035945091)
            ·
              refine ⟨6309715196546809553917637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4206476797697873035945091 6309715196546809553917637)
              ·
                refine ⟨1183071599352526791359557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6309715196546809553917637 1183071599352526791359557)
                ·
                  refine ⟨221825924878598773379917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1183071599352526791359557 221825924878598773379917)
                  ·
                    rfl

theorem cell21_972010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4, 4].length) (baseStart_972010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_972010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_972010 prefixEnd_972010 := by exact prefixLift 972010
  have htrace : WordTrace (prefixWord ++ tailWord_972010) baseStart_972010 baseEnd_972010 := by
    simpa [prefixWord, tailWord_972010, baseEnd_972010] using wordTrace_append hprefix tailTrace_972010
  have hstable : (prefixWord ++ tailWord_972010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972010).length < 2 ^ (prefixWord ++ tailWord_972010).sum := by decide
  have hdescent : baseEnd_972010 < baseStart_972010 := by decide
  rcases family_descends (prefixWord ++ tailWord_972010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972013 : List Nat := [1, 5, 1, 2, 2, 2, 1, 4, 3]
def baseStart_972013 : Nat := 118140960795 + 972013 * 2 ^ 59
def prefixEnd_972013 : Nat := 4983230072969 + 3 ^ 40 * 972013 * 2
def baseEnd_972013 : Nat := 221826609519471434829911

theorem tailTrace_972013 : CollatzResearch.WordTrace tailWord_972013 prefixEnd_972013 221826609519471434829911 := by
  unfold tailWord_972013
  simp only [CollatzResearch.WordTrace]
  refine ⟨35452226627570382449048693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23634817751713588299365795 35452226627570382449048693)
  ·
    refine ⟨3323646246334723354598315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35452226627570382449048693 3323646246334723354598315)
    ·
      refine ⟨4985469369502085031897473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3323646246334723354598315 4985469369502085031897473)
      ·
        refine ⟨3739102027126563773923105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4985469369502085031897473 3739102027126563773923105)
        ·
          refine ⟨2804326520344922830442329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3739102027126563773923105 2804326520344922830442329)
          ·
            refine ⟨2103244890258692122831747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2804326520344922830442329 2103244890258692122831747)
            ·
              refine ⟨3154867335388038184247621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2103244890258692122831747 3154867335388038184247621)
              ·
                refine ⟨591537625385257159546429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3154867335388038184247621 591537625385257159546429)
                ·
                  refine ⟨221826609519471434829911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 591537625385257159546429 221826609519471434829911)
                  ·
                    rfl

theorem cell21_972013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_972013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_972013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_972013 prefixEnd_972013 := by exact prefixLift 972013
  have htrace : WordTrace (prefixWord ++ tailWord_972013) baseStart_972013 baseEnd_972013 := by
    simpa [prefixWord, tailWord_972013, baseEnd_972013] using wordTrace_append hprefix tailTrace_972013
  have hstable : (prefixWord ++ tailWord_972013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972013).length < 2 ^ (prefixWord ++ tailWord_972013).sum := by decide
  have hdescent : baseEnd_972013 < baseStart_972013 := by decide
  rcases family_descends (prefixWord ++ tailWord_972013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972072 : List Nat := [2, 1, 5, 1, 2, 2, 2, 1, 5]
def baseStart_972072 : Nat := 118140960795 + 972072 * 2 ^ 59
def prefixEnd_972072 : Nat := 4983230072969 + 3 ^ 40 * 972072 * 2
def baseEnd_972072 : Nat := 221840074123300443346457

theorem tailTrace_972072 : CollatzResearch.WordTrace tailWord_972072 prefixEnd_972072 221840074123300443346457 := by
  unfold tailWord_972072
  simp only [CollatzResearch.WordTrace]
  refine ⟨17727189267178317762723235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23636252356237757016964313 17727189267178317762723235)
  ·
    refine ⟨26590783900767476644084853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17727189267178317762723235 26590783900767476644084853)
    ·
      refine ⟨2492885990696950935382955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26590783900767476644084853 2492885990696950935382955)
      ·
        refine ⟨3739328986045426403074433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2492885990696950935382955 3739328986045426403074433)
        ·
          refine ⟨2804496739534069802305825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3739328986045426403074433 2804496739534069802305825)
          ·
            refine ⟨2103372554650552351729369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2804496739534069802305825 2103372554650552351729369)
            ·
              refine ⟨1577529415987914263797027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2103372554650552351729369 1577529415987914263797027)
              ·
                refine ⟨2366294123981871395695541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1577529415987914263797027 2366294123981871395695541)
                ·
                  refine ⟨221840074123300443346457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2366294123981871395695541 221840074123300443346457)
                  ·
                    rfl

theorem cell21_972072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 5].length) (baseStart_972072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_972072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_972072 prefixEnd_972072 := by exact prefixLift 972072
  have htrace : WordTrace (prefixWord ++ tailWord_972072) baseStart_972072 baseEnd_972072 := by
    simpa [prefixWord, tailWord_972072, baseEnd_972072] using wordTrace_append hprefix tailTrace_972072
  have hstable : (prefixWord ++ tailWord_972072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972072).length < 2 ^ (prefixWord ++ tailWord_972072).sum := by decide
  have hdescent : baseEnd_972072 < baseStart_972072 := by decide
  rcases family_descends (prefixWord ++ tailWord_972072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972131 : List Nat := [1, 1, 1, 5, 2, 2, 3, 1, 5]
def baseStart_972131 : Nat := 118140960795 + 972131 * 2 ^ 59
def prefixEnd_972131 : Nat := 4983230072969 + 3 ^ 40 * 972131 * 2
def baseEnd_972131 : Nat := 221853538727129451863003

theorem tailTrace_972131 : CollatzResearch.WordTrace tailWord_972131 prefixEnd_972131 221853538727129451863003 := by
  unfold tailWord_972131
  simp only [CollatzResearch.WordTrace]
  refine ⟨35456530441142888601844247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23637686960761925734562831 35456530441142888601844247)
  ·
    refine ⟨53184795661714332902766371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35456530441142888601844247 53184795661714332902766371)
    ·
      refine ⟨79777193492571499354149557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53184795661714332902766371 79777193492571499354149557)
      ·
        refine ⟨7479111889928578064451521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79777193492571499354149557 7479111889928578064451521)
        ·
          refine ⟨5609333917446433548338641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7479111889928578064451521 5609333917446433548338641)
          ·
            refine ⟨4207000438084825161253981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5609333917446433548338641 4207000438084825161253981)
            ·
              refine ⟨1577625164281809435470243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4207000438084825161253981 1577625164281809435470243)
              ·
                refine ⟨2366437746422714153205365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1577625164281809435470243 2366437746422714153205365)
                ·
                  refine ⟨221853538727129451863003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2366437746422714153205365 221853538727129451863003)
                  ·
                    rfl

theorem cell21_972131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 5].length) (baseStart_972131 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_972131 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_972131 prefixEnd_972131 := by exact prefixLift 972131
  have htrace : WordTrace (prefixWord ++ tailWord_972131) baseStart_972131 baseEnd_972131 := by
    simpa [prefixWord, tailWord_972131, baseEnd_972131] using wordTrace_append hprefix tailTrace_972131
  have hstable : (prefixWord ++ tailWord_972131).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972131).length < 2 ^ (prefixWord ++ tailWord_972131).sum := by decide
  have hdescent : baseEnd_972131 < baseStart_972131 := by decide
  rcases family_descends (prefixWord ++ tailWord_972131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972221 : List Nat := [1, 4, 1, 2, 2, 1, 2, 2, 6]
def baseStart_972221 : Nat := 118140960795 + 972221 * 2 ^ 59
def prefixEnd_972221 : Nat := 4983230072969 + 3 ^ 40 * 972221 * 2
def baseEnd_972221 : Nat := 221874077953309295362819

theorem tailTrace_972221 : CollatzResearch.WordTrace tailWord_972221 prefixEnd_972221 221874077953309295362819 := by
  unfold tailWord_972221
  simp only [CollatzResearch.WordTrace]
  refine ⟨35459813010816833972620517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23639875340544555981747011 35459813010816833972620517)
  ·
    refine ⟨6648714939528156369866347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35459813010816833972620517 6648714939528156369866347)
    ·
      refine ⟨9973072409292234554799521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6648714939528156369866347 9973072409292234554799521)
      ·
        refine ⟨7479804306969175916099641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9973072409292234554799521 7479804306969175916099641)
        ·
          refine ⟨5609853230226881937074731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7479804306969175916099641 5609853230226881937074731)
          ·
            refine ⟨8414779845340322905612097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5609853230226881937074731 8414779845340322905612097)
            ·
              refine ⟨6311084884005242179209073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8414779845340322905612097 6311084884005242179209073)
              ·
                refine ⟨4733313663003931634406805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6311084884005242179209073 4733313663003931634406805)
                ·
                  refine ⟨221874077953309295362819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4733313663003931634406805 221874077953309295362819)
                  ·
                    rfl

theorem cell21_972221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_972221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_972221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_972221 prefixEnd_972221 := by exact prefixLift 972221
  have htrace : WordTrace (prefixWord ++ tailWord_972221) baseStart_972221 baseEnd_972221 := by
    simpa [prefixWord, tailWord_972221, baseEnd_972221] using wordTrace_append hprefix tailTrace_972221
  have hstable : (prefixWord ++ tailWord_972221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972221).length < 2 ^ (prefixWord ++ tailWord_972221).sum := by decide
  have hdescent : baseEnd_972221 < baseStart_972221 := by decide
  rcases family_descends (prefixWord ++ tailWord_972221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972238 : List Nat := [4, 1, 1, 1, 2, 1, 5, 2, 4]
def baseStart_972238 : Nat := 118140960795 + 972238 * 2 ^ 59
def prefixEnd_972238 : Nat := 4983230072969 + 3 ^ 40 * 972238 * 2
def baseEnd_972238 : Nat := 221877957584921043579451

theorem tailTrace_972238 : CollatzResearch.WordTrace tailWord_972238 prefixEnd_972238 221877957584921043579451 := by
  unfold tailWord_972238
  simp only [CollatzResearch.WordTrace]
  refine ⟨4432554131469405734498671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23640288701170163917326245 4432554131469405734498671)
  ·
    refine ⟨6648831197204108601748007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4432554131469405734498671 6648831197204108601748007)
    ·
      refine ⟨9973246795806162902622011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6648831197204108601748007 9973246795806162902622011)
      ·
        refine ⟨14959870193709244353933017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9973246795806162902622011 14959870193709244353933017)
        ·
          refine ⟨11219902645281933265449763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14959870193709244353933017 11219902645281933265449763)
          ·
            refine ⟨16829853967922899898174645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11219902645281933265449763 16829853967922899898174645)
            ·
              refine ⟨1577798809492771865453873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16829853967922899898174645 1577798809492771865453873)
              ·
                refine ⟨1183349107119578899090405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1577798809492771865453873 1183349107119578899090405)
                ·
                  refine ⟨221877957584921043579451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1183349107119578899090405 221877957584921043579451)
                  ·
                    rfl

theorem cell21_972238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_972238 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_972238 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_972238 prefixEnd_972238 := by exact prefixLift 972238
  have htrace : WordTrace (prefixWord ++ tailWord_972238) baseStart_972238 baseEnd_972238 := by
    simpa [prefixWord, tailWord_972238, baseEnd_972238] using wordTrace_append hprefix tailTrace_972238
  have hstable : (prefixWord ++ tailWord_972238).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972238).length < 2 ^ (prefixWord ++ tailWord_972238).sum := by decide
  have hdescent : baseEnd_972238 < baseStart_972238 := by decide
  rcases family_descends (prefixWord ++ tailWord_972238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972269 : List Nat := [1, 5, 1, 3, 2, 1, 1, 7]
def baseStart_972269 : Nat := 118140960795 + 972269 * 2 ^ 59
def prefixEnd_972269 : Nat := 4983230072969 + 3 ^ 40 * 972269 * 2
def baseEnd_972269 : Nat := 73961677402423959520907

theorem tailTrace_972269 : CollatzResearch.WordTrace tailWord_972269 prefixEnd_972269 73961677402423959520907 := by
  unfold tailWord_972269
  simp only [CollatzResearch.WordTrace]
  refine ⟨35461563714642938170367861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23641042476428625446911907 35461563714642938170367861)
  ·
    refine ⟨3324521598247775453471987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35461563714642938170367861 3324521598247775453471987)
    ·
      refine ⟨4986782397371663180207981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3324521598247775453471987 4986782397371663180207981)
      ·
        refine ⟨1870043399014373692577993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4986782397371663180207981 1870043399014373692577993)
        ·
          refine ⟨1402532549260780269433495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1870043399014373692577993 1402532549260780269433495)
          ·
            refine ⟨2103798823891170404150243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1402532549260780269433495 2103798823891170404150243)
            ·
              refine ⟨3155698235836755606225365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2103798823891170404150243 3155698235836755606225365)
              ·
                refine ⟨73961677402423959520907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3155698235836755606225365 73961677402423959520907)
                ·
                  rfl

theorem cell21_972269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 7].length) (baseStart_972269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_972269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_972269 prefixEnd_972269 := by exact prefixLift 972269
  have htrace : WordTrace (prefixWord ++ tailWord_972269) baseStart_972269 baseEnd_972269 := by
    simpa [prefixWord, tailWord_972269, baseEnd_972269] using wordTrace_append hprefix tailTrace_972269
  have hstable : (prefixWord ++ tailWord_972269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972269).length < 2 ^ (prefixWord ++ tailWord_972269).sum := by decide
  have hdescent : baseEnd_972269 < baseStart_972269 := by decide
  rcases family_descends (prefixWord ++ tailWord_972269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972286 : List Nat := [4, 2, 2, 3, 1, 2, 7]
def baseStart_972286 : Nat := 118140960795 + 972286 * 2 ^ 59
def prefixEnd_972286 : Nat := 4983230072969 + 3 ^ 40 * 972286 * 2
def baseEnd_972286 : Nat := 24654323537653736308817

theorem tailTrace_972286 : CollatzResearch.WordTrace tailWord_972286 prefixEnd_972286 24654323537653736308817 := by
  unfold tailWord_972286
  simp only [CollatzResearch.WordTrace]
  refine ⟨4432772969447668759217089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23641455837054233382491141 4432772969447668759217089)
  ·
    refine ⟨3324579727085751569412817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4432772969447668759217089 3324579727085751569412817)
    ·
      refine ⟨2493434795314313677059613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3324579727085751569412817 2493434795314313677059613)
      ·
        refine ⟨935038048242867628897355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2493434795314313677059613 935038048242867628897355)
        ·
          refine ⟨1402557072364301443346033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 935038048242867628897355 1402557072364301443346033)
          ·
            refine ⟨1051917804273226082509525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1402557072364301443346033 1051917804273226082509525)
            ·
              refine ⟨24654323537653736308817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1051917804273226082509525 24654323537653736308817)
              ·
                rfl

theorem cell21_972286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 7].length) (baseStart_972286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_972286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_972286 prefixEnd_972286 := by exact prefixLift 972286
  have htrace : WordTrace (prefixWord ++ tailWord_972286) baseStart_972286 baseEnd_972286 := by
    simpa [prefixWord, tailWord_972286, baseEnd_972286] using wordTrace_append hprefix tailTrace_972286
  have hstable : (prefixWord ++ tailWord_972286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972286).length < 2 ^ (prefixWord ++ tailWord_972286).sum := by decide
  have hdescent : baseEnd_972286 < baseStart_972286 := by decide
  rcases family_descends (prefixWord ++ tailWord_972286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972297 : List Nat := [1, 2, 1, 1, 3, 1, 4, 4, 4]
def baseStart_972297 : Nat := 118140960795 + 972297 * 2 ^ 59
def prefixEnd_972297 : Nat := 4983230072969 + 3 ^ 40 * 972297 * 2
def baseEnd_972297 : Nat := 221891422188750052095997

theorem tailTrace_972297 : CollatzResearch.WordTrace tailWord_972297 prefixEnd_972297 221891422188750052095997 := by
  unfold tailWord_972297
  simp only [CollatzResearch.WordTrace]
  refine ⟨35462584958541498952387145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23641723305694332634924763 35462584958541498952387145)
  ·
    refine ⟨26596938718906124214290359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35462584958541498952387145 26596938718906124214290359)
    ·
      refine ⟨39895408078359186321435539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26596938718906124214290359 39895408078359186321435539)
      ·
        refine ⟨59843112117538779482153309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39895408078359186321435539 59843112117538779482153309)
        ·
          refine ⟨22441167044077042305807491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59843112117538779482153309 22441167044077042305807491)
          ·
            refine ⟨33661750566115563458711237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22441167044077042305807491 33661750566115563458711237)
            ·
              refine ⟨6311578231146668148508357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33661750566115563458711237 6311578231146668148508357)
              ·
                refine ⟨1183420918340000277845317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6311578231146668148508357 1183420918340000277845317)
                ·
                  refine ⟨221891422188750052095997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1183420918340000277845317 221891422188750052095997)
                  ·
                    rfl

theorem cell21_972297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4, 4].length) (baseStart_972297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_972297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_972297 prefixEnd_972297 := by exact prefixLift 972297
  have htrace : WordTrace (prefixWord ++ tailWord_972297) baseStart_972297 baseEnd_972297 := by
    simpa [prefixWord, tailWord_972297, baseEnd_972297] using wordTrace_append hprefix tailTrace_972297
  have hstable : (prefixWord ++ tailWord_972297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972297).length < 2 ^ (prefixWord ++ tailWord_972297).sum := by decide
  have hdescent : baseEnd_972297 < baseStart_972297 := by decide
  rcases family_descends (prefixWord ++ tailWord_972297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972300 : List Nat := [2, 2, 1, 2, 5, 2, 1, 1, 5]
def baseStart_972300 : Nat := 118140960795 + 972300 * 2 ^ 59
def prefixEnd_972300 : Nat := 4983230072969 + 3 ^ 40 * 972300 * 2
def baseEnd_972300 : Nat := 221892106829622713545991

theorem tailTrace_972300 : CollatzResearch.WordTrace tailWord_972300 prefixEnd_972300 221892106829622713545991 := by
  unfold tailWord_972300
  simp only [CollatzResearch.WordTrace]
  refine ⟨17731347188765315232373177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23641796251687086976497569 17731347188765315232373177)
  ·
    refine ⟨13298510391573986424279883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17731347188765315232373177 13298510391573986424279883)
    ·
      refine ⟨19947765587360979636419825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13298510391573986424279883 19947765587360979636419825)
      ·
        refine ⟨14960824190520734727314869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19947765587360979636419825 14960824190520734727314869)
        ·
          refine ⟨1402577267861318880685769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14960824190520734727314869 1402577267861318880685769)
          ·
            refine ⟨1051932950895989160514327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1402577267861318880685769 1051932950895989160514327)
            ·
              refine ⟨1577899426343983740771491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1051932950895989160514327 1577899426343983740771491)
              ·
                refine ⟨2366849139515975611157237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1577899426343983740771491 2366849139515975611157237)
                ·
                  refine ⟨221892106829622713545991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2366849139515975611157237 221892106829622713545991)
                  ·
                    rfl

theorem cell21_972300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 5].length) (baseStart_972300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_972300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_972300 prefixEnd_972300 := by exact prefixLift 972300
  have htrace : WordTrace (prefixWord ++ tailWord_972300) baseStart_972300 baseEnd_972300 := by
    simpa [prefixWord, tailWord_972300, baseEnd_972300] using wordTrace_append hprefix tailTrace_972300
  have hstable : (prefixWord ++ tailWord_972300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972300).length < 2 ^ (prefixWord ++ tailWord_972300).sum := by decide
  have hdescent : baseEnd_972300 < baseStart_972300 := by decide
  rcases family_descends (prefixWord ++ tailWord_972300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972424 : List Nat := [2, 1, 3, 5, 1, 1, 3, 1, 4]
def baseStart_972424 : Nat := 118140960795 + 972424 * 2 ^ 59
def prefixEnd_972424 : Nat := 4983230072969 + 3 ^ 40 * 972424 * 2
def baseEnd_972424 : Nat := 221920405319026053479071

theorem tailTrace_972424 : CollatzResearch.WordTrace tailWord_972424 prefixEnd_972424 221920405319026053479071 := by
  unfold tailWord_972424
  simp only [CollatzResearch.WordTrace]
  refine ⟨17733608514540699821130163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23644811352720933094840217 17733608514540699821130163)
  ·
    refine ⟨26600412771811049731695245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17733608514540699821130163 26600412771811049731695245)
    ·
      refine ⟨9975154789429143649385717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26600412771811049731695245 9975154789429143649385717)
      ·
        refine ⟨935170761508982217129911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9975154789429143649385717 935170761508982217129911)
        ·
          refine ⟨1402756142263473325694867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 935170761508982217129911 1402756142263473325694867)
          ·
            refine ⟨2104134213395209988542301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1402756142263473325694867 2104134213395209988542301)
            ·
              refine ⟨789050330023203745703363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2104134213395209988542301 789050330023203745703363)
              ·
                refine ⟨1183575495034805618555045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 789050330023203745703363 1183575495034805618555045)
                ·
                  refine ⟨221920405319026053479071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1183575495034805618555045 221920405319026053479071)
                  ·
                    rfl

theorem cell21_972424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 1, 4].length) (baseStart_972424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_972424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_972424 prefixEnd_972424 := by exact prefixLift 972424
  have htrace : WordTrace (prefixWord ++ tailWord_972424) baseStart_972424 baseEnd_972424 := by
    simpa [prefixWord, tailWord_972424, baseEnd_972424] using wordTrace_append hprefix tailTrace_972424
  have hstable : (prefixWord ++ tailWord_972424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972424).length < 2 ^ (prefixWord ++ tailWord_972424).sum := by decide
  have hdescent : baseEnd_972424 < baseStart_972424 := by decide
  rcases family_descends (prefixWord ++ tailWord_972424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972449 : List Nat := [1, 2, 3, 3, 2, 1, 1, 2, 6]
def baseStart_972449 : Nat := 118140960795 + 972449 * 2 ^ 59
def prefixEnd_972449 : Nat := 4983230072969 + 3 ^ 40 * 972449 * 2
def baseEnd_972449 : Nat := 221926110659631565562353

theorem tailTrace_972449 : CollatzResearch.WordTrace tailWord_972449 prefixEnd_972449 221926110659631565562353 := by
  unfold tailWord_972449
  simp only [CollatzResearch.WordTrace]
  refine ⟨35468128853990828911920401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23645419235993885941280267 35468128853990828911920401)
  ·
    refine ⟨26601096640493121683940301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35468128853990828911920401 26601096640493121683940301)
    ·
      refine ⟨9975411240184920631477613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26601096640493121683940301 9975411240184920631477613)
      ·
        refine ⟨3740779215069345236804105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9975411240184920631477613 3740779215069345236804105)
        ·
          refine ⟨2805584411302008927603079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3740779215069345236804105 2805584411302008927603079)
          ·
            refine ⟨4208376616953013391404619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2805584411302008927603079 4208376616953013391404619)
            ·
              refine ⟨6312564925429520087106929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4208376616953013391404619 6312564925429520087106929)
              ·
                refine ⟨4734423694072140065330197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6312564925429520087106929 4734423694072140065330197)
                ·
                  refine ⟨221926110659631565562353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4734423694072140065330197 221926110659631565562353)
                  ·
                    rfl

theorem cell21_972449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 6].length) (baseStart_972449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_972449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_972449 prefixEnd_972449 := by exact prefixLift 972449
  have htrace : WordTrace (prefixWord ++ tailWord_972449) baseStart_972449 baseEnd_972449 := by
    simpa [prefixWord, tailWord_972449, baseEnd_972449] using wordTrace_append hprefix tailTrace_972449
  have hstable : (prefixWord ++ tailWord_972449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972449).length < 2 ^ (prefixWord ++ tailWord_972449).sum := by decide
  have hdescent : baseEnd_972449 < baseStart_972449 := by decide
  rcases family_descends (prefixWord ++ tailWord_972449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972452 : List Nat := [2, 3, 1, 2, 2, 2, 3, 3, 3]
def baseStart_972452 : Nat := 118140960795 + 972452 * 2 ^ 59
def prefixEnd_972452 : Nat := 4983230072969 + 3 ^ 40 * 972452 * 2
def baseEnd_972452 : Nat := 221926795300504227012347

theorem tailTrace_972452 : CollatzResearch.WordTrace tailWord_972452 prefixEnd_972452 221926795300504227012347 := by
  unfold tailWord_972452
  simp only [CollatzResearch.WordTrace]
  refine ⟨17734119136489980212139805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23645492181986640282853073 17734119136489980212139805)
  ·
    refine ⟨6650294676183742579552427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17734119136489980212139805 6650294676183742579552427)
    ·
      refine ⟨9975442014275613869328641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6650294676183742579552427 9975442014275613869328641)
      ·
        refine ⟨7481581510706710401996481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9975442014275613869328641 7481581510706710401996481)
        ·
          refine ⟨5611186133030032801497361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7481581510706710401996481 5611186133030032801497361)
          ·
            refine ⟨4208389599772524601123021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5611186133030032801497361 4208389599772524601123021)
            ·
              refine ⟨1578146099914696725421133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4208389599772524601123021 1578146099914696725421133)
              ·
                refine ⟨591804787468011272032925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1578146099914696725421133 591804787468011272032925)
                ·
                  refine ⟨221926795300504227012347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 591804787468011272032925 221926795300504227012347)
                  ·
                    rfl

theorem cell21_972452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 3, 3].length) (baseStart_972452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_972452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_972452 prefixEnd_972452 := by exact prefixLift 972452
  have htrace : WordTrace (prefixWord ++ tailWord_972452) baseStart_972452 baseEnd_972452 := by
    simpa [prefixWord, tailWord_972452, baseEnd_972452] using wordTrace_append hprefix tailTrace_972452
  have hstable : (prefixWord ++ tailWord_972452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972452).length < 2 ^ (prefixWord ++ tailWord_972452).sum := by decide
  have hdescent : baseEnd_972452 < baseStart_972452 := by decide
  rcases family_descends (prefixWord ++ tailWord_972452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972469 : List Nat := [1, 3, 3, 3, 3, 1, 1, 1, 5]
def baseStart_972469 : Nat := 118140960795 + 972469 * 2 ^ 59
def prefixEnd_972469 : Nat := 4983230072969 + 3 ^ 40 * 972469 * 2
def baseEnd_972469 : Nat := 221930674932115975228979

theorem tailTrace_972469 : CollatzResearch.WordTrace tailWord_972469 prefixEnd_972469 221930674932115975228979 := by
  unfold tailWord_972469
  simp only [CollatzResearch.WordTrace]
  refine ⟨35468858313918372327648461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23645905542612248218432307 35468858313918372327648461)
  ·
    refine ⟨13300821867719389622868173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35468858313918372327648461 13300821867719389622868173)
    ·
      refine ⟨4987808200394771108575565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13300821867719389622868173 4987808200394771108575565)
      ·
        refine ⟨1870428075148039165715837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4987808200394771108575565 1870428075148039165715837)
        ·
          refine ⟨701410528180514687143439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1870428075148039165715837 701410528180514687143439)
          ·
            refine ⟨1052115792270772030715159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 701410528180514687143439 1052115792270772030715159)
            ·
              refine ⟨1578173688406158046072739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1052115792270772030715159 1578173688406158046072739)
              ·
                refine ⟨2367260532609237069109109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1578173688406158046072739 2367260532609237069109109)
                ·
                  refine ⟨221930674932115975228979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2367260532609237069109109 221930674932115975228979)
                  ·
                    rfl

theorem cell21_972469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 5].length) (baseStart_972469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_972469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_972469 prefixEnd_972469 := by exact prefixLift 972469
  have htrace : WordTrace (prefixWord ++ tailWord_972469) baseStart_972469 baseEnd_972469 := by
    simpa [prefixWord, tailWord_972469, baseEnd_972469] using wordTrace_append hprefix tailTrace_972469
  have hstable : (prefixWord ++ tailWord_972469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972469).length < 2 ^ (prefixWord ++ tailWord_972469).sum := by decide
  have hdescent : baseEnd_972469 < baseStart_972469 := by decide
  rcases family_descends (prefixWord ++ tailWord_972469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972494 : List Nat := [4, 1, 1, 1, 3, 1, 2, 1, 7]
def baseStart_972494 : Nat := 118140960795 + 972494 * 2 ^ 59
def prefixEnd_972494 : Nat := 4983230072969 + 3 ^ 40 * 972494 * 2
def baseEnd_972494 : Nat := 221936380272721487312261

theorem tailTrace_972494 : CollatzResearch.WordTrace tailWord_972494 prefixEnd_972494 221936380272721487312261 := by
  unfold tailWord_972494
  simp only [CollatzResearch.WordTrace]
  refine ⟨4433721267353475199663567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23646513425885201064872357 4433721267353475199663567)
  ·
    refine ⟨6650581901030212799495351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4433721267353475199663567 6650581901030212799495351)
    ·
      refine ⟨9975872851545319199243027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6650581901030212799495351 9975872851545319199243027)
      ·
        refine ⟨14963809277317978798864541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9975872851545319199243027 14963809277317978798864541)
        ·
          refine ⟨5611428478994242049574203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14963809277317978798864541 5611428478994242049574203)
          ·
            refine ⟨8417142718491363074361305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5611428478994242049574203 8417142718491363074361305)
            ·
              refine ⟨6312857038868522305770979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8417142718491363074361305 6312857038868522305770979)
              ·
                refine ⟨9469285558302783458656469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6312857038868522305770979 9469285558302783458656469)
                ·
                  refine ⟨221936380272721487312261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9469285558302783458656469 221936380272721487312261)
                  ·
                    rfl

theorem cell21_972494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_972494 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_972494 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_972494 prefixEnd_972494 := by exact prefixLift 972494
  have htrace : WordTrace (prefixWord ++ tailWord_972494) baseStart_972494 baseEnd_972494 := by
    simpa [prefixWord, tailWord_972494, baseEnd_972494] using wordTrace_append hprefix tailTrace_972494
  have hstable : (prefixWord ++ tailWord_972494).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972494).length < 2 ^ (prefixWord ++ tailWord_972494).sum := by decide
  have hdescent : baseEnd_972494 < baseStart_972494 := by decide
  rcases family_descends (prefixWord ++ tailWord_972494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972511 : List Nat := [1, 1, 2, 3, 2, 2, 2, 5, 3]
def baseStart_972511 : Nat := 118140960795 + 972511 * 2 ^ 59
def prefixEnd_972511 : Nat := 4983230072969 + 3 ^ 40 * 972511 * 2
def baseEnd_972511 : Nat := 221940259904333235528893

theorem tailTrace_972511 : CollatzResearch.WordTrace tailWord_972511 prefixEnd_972511 221940259904333235528893 := by
  unfold tailWord_972511
  simp only [CollatzResearch.WordTrace]
  refine ⟨35470390179766213500677387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23646926786510809000451591 35470390179766213500677387)
  ·
    refine ⟨53205585269649320251016081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35470390179766213500677387 53205585269649320251016081)
    ·
      refine ⟨39904188952236990188262061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53205585269649320251016081 39904188952236990188262061)
      ·
        refine ⟨14964070857088871320598273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39904188952236990188262061 14964070857088871320598273)
        ·
          refine ⟨11223053142816653490448705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14964070857088871320598273 11223053142816653490448705)
          ·
            refine ⟨8417289857112490117836529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11223053142816653490448705 8417289857112490117836529)
            ·
              refine ⟨6312967392834367588377397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8417289857112490117836529 6312967392834367588377397)
              ·
                refine ⟨591840693078221961410381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6312967392834367588377397 591840693078221961410381)
                ·
                  refine ⟨221940259904333235528893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 591840693078221961410381 221940259904333235528893)
                  ·
                    rfl

theorem cell21_972511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 5, 3].length) (baseStart_972511 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_972511 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_972511 prefixEnd_972511 := by exact prefixLift 972511
  have htrace : WordTrace (prefixWord ++ tailWord_972511) baseStart_972511 baseEnd_972511 := by
    simpa [prefixWord, tailWord_972511, baseEnd_972511] using wordTrace_append hprefix tailTrace_972511
  have hstable : (prefixWord ++ tailWord_972511).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972511).length < 2 ^ (prefixWord ++ tailWord_972511).sum := by decide
  have hdescent : baseEnd_972511 < baseStart_972511 := by decide
  rcases family_descends (prefixWord ++ tailWord_972511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972621 : List Nat := [1, 6, 1, 2, 1, 1, 3, 3, 3]
def baseStart_972621 : Nat := 118140960795 + 972621 * 2 ^ 59
def prefixEnd_972621 : Nat := 4983230072969 + 3 ^ 40 * 972621 * 2
def baseEnd_972621 : Nat := 221965363402997488695335

theorem tailTrace_972621 : CollatzResearch.WordTrace tailWord_972621 prefixEnd_972621 221965363402997488695335 := by
  unfold tailWord_972621
  simp only [CollatzResearch.WordTrace]
  refine ⟨35474402209367702287181717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23649601472911801524787811 35474402209367702287181717)
  ·
    refine ⟨1662862603564111044711643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35474402209367702287181717 1662862603564111044711643)
    ·
      refine ⟨2494293905346166567067465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1662862603564111044711643 2494293905346166567067465)
      ·
        refine ⟨1870720429009624925300599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2494293905346166567067465 1870720429009624925300599)
        ·
          refine ⟨2806080643514437387950899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1870720429009624925300599 2806080643514437387950899)
          ·
            refine ⟨4209120965271656081926349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2806080643514437387950899 4209120965271656081926349)
            ·
              refine ⟨1578420361976871030722381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4209120965271656081926349 1578420361976871030722381)
              ·
                refine ⟨591907635741326636520893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1578420361976871030722381 591907635741326636520893)
                ·
                  refine ⟨221965363402997488695335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 591907635741326636520893 221965363402997488695335)
                  ·
                    rfl

theorem cell21_972621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_972621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_972621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_972621 prefixEnd_972621 := by exact prefixLift 972621
  have htrace : WordTrace (prefixWord ++ tailWord_972621) baseStart_972621 baseEnd_972621 := by
    simpa [prefixWord, tailWord_972621, baseEnd_972621] using wordTrace_append hprefix tailTrace_972621
  have hstable : (prefixWord ++ tailWord_972621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972621).length < 2 ^ (prefixWord ++ tailWord_972621).sum := by decide
  have hdescent : baseEnd_972621 < baseStart_972621 := by decide
  rcases family_descends (prefixWord ++ tailWord_972621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972708 : List Nat := [2, 3, 1, 2, 1, 5, 1, 6]
def baseStart_972708 : Nat := 118140960795 + 972708 * 2 ^ 59
def prefixEnd_972708 : Nat := 4983230072969 + 3 ^ 40 * 972708 * 2
def baseEnd_972708 : Nat := 73995072662768223581719

theorem tailTrace_972708 : CollatzResearch.WordTrace tailWord_972708 prefixEnd_972708 73995072662768223581719 := by
  unfold tailWord_972708
  simp only [CollatzResearch.WordTrace]
  refine ⟨17738787680026258072799389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23651716906701677430399185 17738787680026258072799389)
  ·
    refine ⟨6652045380009846777299771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17738787680026258072799389 6652045380009846777299771)
    ·
      refine ⟨9978068070014770165949657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6652045380009846777299771 9978068070014770165949657)
      ·
        refine ⟨7483551052511077624462243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9978068070014770165949657 7483551052511077624462243)
        ·
          refine ⟨11225326578766616436693365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7483551052511077624462243 11225326578766616436693365)
          ·
            refine ⟨1052374366759370290940003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11225326578766616436693365 1052374366759370290940003)
            ·
              refine ⟨1578561550139055436410005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1052374366759370290940003 1578561550139055436410005)
              ·
                refine ⟨73995072662768223581719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1578561550139055436410005 73995072662768223581719)
                ·
                  rfl

theorem cell21_972708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 6].length) (baseStart_972708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_972708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_972708 prefixEnd_972708 := by exact prefixLift 972708
  have htrace : WordTrace (prefixWord ++ tailWord_972708) baseStart_972708 baseEnd_972708 := by
    simpa [prefixWord, tailWord_972708, baseEnd_972708] using wordTrace_append hprefix tailTrace_972708
  have hstable : (prefixWord ++ tailWord_972708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972708).length < 2 ^ (prefixWord ++ tailWord_972708).sum := by decide
  have hdescent : baseEnd_972708 < baseStart_972708 := by decide
  rcases family_descends (prefixWord ++ tailWord_972708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972736 : List Nat := [2, 1, 1, 2, 3, 2, 2, 2, 6]
def baseStart_972736 : Nat := 118140960795 + 972736 * 2 ^ 59
def prefixEnd_972736 : Nat := 4983230072969 + 3 ^ 40 * 972736 * 2
def baseEnd_972736 : Nat := 221991607969782844278433

theorem tailTrace_972736 : CollatzResearch.WordTrace tailWord_972736 prefixEnd_972736 221991607969782844278433 := by
  unfold tailWord_972736
  simp only [CollatzResearch.WordTrace]
  refine ⟨17739298301975538463809031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23652397735967384618412041 17739298301975538463809031)
  ·
    refine ⟨26608947452963307695713547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17739298301975538463809031 26608947452963307695713547)
    ·
      refine ⟨39913421179444961543570321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26608947452963307695713547 39913421179444961543570321)
      ·
        refine ⟨29935065884583721157677741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39913421179444961543570321 29935065884583721157677741)
        ·
          refine ⟨11225649706718895434129153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29935065884583721157677741 11225649706718895434129153)
          ·
            refine ⟨8419237280039171575596865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11225649706718895434129153 8419237280039171575596865)
            ·
              refine ⟨6314427960029378681697649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8419237280039171575596865 6314427960029378681697649)
              ·
                refine ⟨4735820970022034011273237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6314427960029378681697649 4735820970022034011273237)
                ·
                  refine ⟨221991607969782844278433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4735820970022034011273237 221991607969782844278433)
                  ·
                    rfl

theorem cell21_972736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 6].length) (baseStart_972736 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_972736 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_972736 prefixEnd_972736 := by exact prefixLift 972736
  have htrace : WordTrace (prefixWord ++ tailWord_972736) baseStart_972736 baseEnd_972736 := by
    simpa [prefixWord, tailWord_972736, baseEnd_972736] using wordTrace_append hprefix tailTrace_972736
  have hstable : (prefixWord ++ tailWord_972736).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972736).length < 2 ^ (prefixWord ++ tailWord_972736).sum := by decide
  have hdescent : baseEnd_972736 < baseStart_972736 := by decide
  rcases family_descends (prefixWord ++ tailWord_972736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972790 : List Nat := [5, 1, 1, 1, 5, 1, 1, 3, 3]
def baseStart_972790 : Nat := 118140960795 + 972790 * 2 ^ 59
def prefixEnd_972790 : Nat := 4983230072969 + 3 ^ 40 * 972790 * 2
def baseEnd_972790 : Nat := 222003931505490750378323

theorem tailTrace_972790 : CollatzResearch.WordTrace tailWord_972790 prefixEnd_972790 222003931505490750378323 := by
  unfold tailWord_972790
  simp only [CollatzResearch.WordTrace]
  refine ⟨2217535384109715259380239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23653710763836962766722549 2217535384109715259380239)
  ·
    refine ⟨3326303076164572889070359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2217535384109715259380239 3326303076164572889070359)
    ·
      refine ⟨4989454614246859333605539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3326303076164572889070359 4989454614246859333605539)
      ·
        refine ⟨7484181921370289000408309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4989454614246859333605539 7484181921370289000408309)
        ·
          refine ⟨701642055128464593788279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7484181921370289000408309 701642055128464593788279)
          ·
            refine ⟨1052463082692696890682419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 701642055128464593788279 1052463082692696890682419)
            ·
              refine ⟨1578694624039045336023629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1052463082692696890682419 1578694624039045336023629)
              ·
                refine ⟨592010484014642001008861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1578694624039045336023629 592010484014642001008861)
                ·
                  refine ⟨222003931505490750378323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 592010484014642001008861 222003931505490750378323)
                  ·
                    rfl

theorem cell21_972790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_972790 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_972790 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_972790 prefixEnd_972790 := by exact prefixLift 972790
  have htrace : WordTrace (prefixWord ++ tailWord_972790) baseStart_972790 baseEnd_972790 := by
    simpa [prefixWord, tailWord_972790, baseEnd_972790] using wordTrace_append hprefix tailTrace_972790
  have hstable : (prefixWord ++ tailWord_972790).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972790).length < 2 ^ (prefixWord ++ tailWord_972790).sum := by decide
  have hdescent : baseEnd_972790 < baseStart_972790 := by decide
  rcases family_descends (prefixWord ++ tailWord_972790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_972812 : List Nat := [2, 2, 1, 2, 3, 1, 1, 3, 6]
def baseStart_972812 : Nat := 118140960795 + 972812 * 2 ^ 59
def prefixEnd_972812 : Nat := 4983230072969 + 3 ^ 40 * 972812 * 2
def baseEnd_972812 : Nat := 222008952205223601011611

theorem tailTrace_972812 : CollatzResearch.WordTrace tailWord_972812 prefixEnd_972812 222008952205223601011611 := by
  unfold tailWord_972812
  simp only [CollatzResearch.WordTrace]
  refine ⟨17740684275837870953692345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23654245701117161271589793 17740684275837870953692345)
  ·
    refine ⟨13305513206878403215269259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17740684275837870953692345 13305513206878403215269259)
    ·
      refine ⟨19958269810317604822903889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13305513206878403215269259 19958269810317604822903889)
      ·
        refine ⟨14968702357738203617177917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19958269810317604822903889 14968702357738203617177917)
        ·
          refine ⟨5613263384151826356441719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14968702357738203617177917 5613263384151826356441719)
          ·
            refine ⟨8419895076227739534662579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5613263384151826356441719 8419895076227739534662579)
            ·
              refine ⟨12629842614341609301993869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8419895076227739534662579 12629842614341609301993869)
              ·
                refine ⟨4736190980378103488247701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12629842614341609301993869 4736190980378103488247701)
                ·
                  refine ⟨222008952205223601011611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4736190980378103488247701 222008952205223601011611)
                  ·
                    rfl

theorem cell21_972812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_972812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_972812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_972812 prefixEnd_972812 := by exact prefixLift 972812
  have htrace : WordTrace (prefixWord ++ tailWord_972812) baseStart_972812 baseEnd_972812 := by
    simpa [prefixWord, tailWord_972812, baseEnd_972812] using wordTrace_append hprefix tailTrace_972812
  have hstable : (prefixWord ++ tailWord_972812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_972812).length < 2 ^ (prefixWord ++ tailWord_972812).sum := by decide
  have hdescent : baseEnd_972812 < baseStart_972812 := by decide
  rcases family_descends (prefixWord ++ tailWord_972812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973009 : List Nat := [1, 2, 2, 1, 2, 2, 2, 4, 5]
def baseStart_973009 : Nat := 118140960795 + 973009 * 2 ^ 59
def prefixEnd_973009 : Nat := 4983230072969 + 3 ^ 40 * 973009 * 2
def baseEnd_973009 : Nat := 222053910289195036227875

theorem tailTrace_973009 : CollatzResearch.WordTrace tailWord_973009 prefixEnd_973009 222053910289195036227875 := by
  unfold tailWord_973009
  simp only [CollatzResearch.WordTrace]
  refine ⟨35488553731962044552306081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23659035821308029701537387 35488553731962044552306081)
  ·
    refine ⟨26616415298971533414229561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35488553731962044552306081 26616415298971533414229561)
    ·
      refine ⟨19962311474228650060672171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26616415298971533414229561 19962311474228650060672171)
      ·
        refine ⟨29943467211342975091008257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19962311474228650060672171 29943467211342975091008257)
        ·
          refine ⟨22457600408507231318256193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29943467211342975091008257 22457600408507231318256193)
          ·
            refine ⟨16843200306380423488692145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22457600408507231318256193 16843200306380423488692145)
            ·
              refine ⟨12632400229785317616519109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16843200306380423488692145 12632400229785317616519109)
              ·
                refine ⟨2368575043084747053097333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12632400229785317616519109 2368575043084747053097333)
                ·
                  refine ⟨222053910289195036227875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2368575043084747053097333 222053910289195036227875)
                  ·
                    rfl

theorem cell21_973009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 5].length) (baseStart_973009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_973009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_973009 prefixEnd_973009 := by exact prefixLift 973009
  have htrace : WordTrace (prefixWord ++ tailWord_973009) baseStart_973009 baseEnd_973009 := by
    simpa [prefixWord, tailWord_973009, baseEnd_973009] using wordTrace_append hprefix tailTrace_973009
  have hstable : (prefixWord ++ tailWord_973009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973009).length < 2 ^ (prefixWord ++ tailWord_973009).sum := by decide
  have hdescent : baseEnd_973009 < baseStart_973009 := by decide
  rcases family_descends (prefixWord ++ tailWord_973009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973175 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 8]
def baseStart_973175 : Nat := 118140960795 + 973175 * 2 ^ 59
def prefixEnd_973175 : Nat := 4983230072969 + 3 ^ 40 * 973175 * 2
def baseEnd_973175 : Nat := 222091793750815636460869

theorem tailTrace_973175 : CollatzResearch.WordTrace tailWord_973175 prefixEnd_973175 222091793750815636460869 := by
  unfold tailWord_973175
  simp only [CollatzResearch.WordTrace]
  refine ⟨35494608249360654902848979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23663072166240436601899319 35494608249360654902848979)
  ·
    refine ⟨53241912374040982354273469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35494608249360654902848979 53241912374040982354273469)
    ·
      refine ⟨19965717140265368382852551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53241912374040982354273469 19965717140265368382852551)
      ·
        refine ⟨29948575710398052574278827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19965717140265368382852551 29948575710398052574278827)
        ·
          refine ⟨44922863565597078861418241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29948575710398052574278827 44922863565597078861418241)
          ·
            refine ⟨33692147674197809146063681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44922863565597078861418241 33692147674197809146063681)
            ·
              refine ⟨25269110755648356859547761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33692147674197809146063681 25269110755648356859547761)
              ·
                refine ⟨18951833066736267644660821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25269110755648356859547761 18951833066736267644660821)
                ·
                  refine ⟨222091793750815636460869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18951833066736267644660821 222091793750815636460869)
                  ·
                    rfl

theorem cell21_973175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 8].length) (baseStart_973175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_973175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_973175 prefixEnd_973175 := by exact prefixLift 973175
  have htrace : WordTrace (prefixWord ++ tailWord_973175) baseStart_973175 baseEnd_973175 := by
    simpa [prefixWord, tailWord_973175, baseEnd_973175] using wordTrace_append hprefix tailTrace_973175
  have hstable : (prefixWord ++ tailWord_973175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973175).length < 2 ^ (prefixWord ++ tailWord_973175).sum := by decide
  have hdescent : baseEnd_973175 < baseStart_973175 := by decide
  rcases family_descends (prefixWord ++ tailWord_973175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973223 : List Nat := [1, 1, 6, 1, 1, 2, 3, 6]
def baseStart_973223 : Nat := 118140960795 + 973223 * 2 ^ 59
def prefixEnd_973223 : Nat := 4983230072969 + 3 ^ 40 * 973223 * 2
def baseEnd_973223 : Nat := 74034249334926073220257

theorem tailTrace_973223 : CollatzResearch.WordTrace tailWord_973223 prefixEnd_973223 74034249334926073220257 := by
  unfold tailWord_973223
  simp only [CollatzResearch.WordTrace]
  refine ⟨35496358953186759100596323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23664239302124506067064215 35496358953186759100596323)
  ·
    refine ⟨53244538429780138650894485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35496358953186759100596323 53244538429780138650894485)
    ·
      refine ⟨2495837738895943999260679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 53244538429780138650894485 2495837738895943999260679)
      ·
        refine ⟨3743756608343915998891019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2495837738895943999260679 3743756608343915998891019)
        ·
          refine ⟨5615634912515873998336529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3743756608343915998891019 5615634912515873998336529)
          ·
            refine ⟨4211726184386905498752397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5615634912515873998336529 4211726184386905498752397)
            ·
              refine ⟨1579397319145089562032149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4211726184386905498752397 1579397319145089562032149)
              ·
                refine ⟨74034249334926073220257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1579397319145089562032149 74034249334926073220257)
                ·
                  rfl

theorem cell21_973223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 6].length) (baseStart_973223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_973223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_973223 prefixEnd_973223 := by exact prefixLift 973223
  have htrace : WordTrace (prefixWord ++ tailWord_973223) baseStart_973223 baseEnd_973223 := by
    simpa [prefixWord, tailWord_973223, baseEnd_973223] using wordTrace_append hprefix tailTrace_973223
  have hstable : (prefixWord ++ tailWord_973223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973223).length < 2 ^ (prefixWord ++ tailWord_973223).sum := by decide
  have hdescent : baseEnd_973223 < baseStart_973223 := by decide
  rcases family_descends (prefixWord ++ tailWord_973223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973251 : List Nat := [1, 1, 1, 3, 1, 1, 3, 4, 6]
def baseStart_973251 : Nat := 118140960795 + 973251 * 2 ^ 59
def prefixEnd_973251 : Nat := 4983230072969 + 3 ^ 40 * 973251 * 2
def baseEnd_973251 : Nat := 222109137986256393194047

theorem tailTrace_973251 : CollatzResearch.WordTrace tailWord_973251 prefixEnd_973251 222109137986256393194047 := by
  unfold tailWord_973251
  simp only [CollatzResearch.WordTrace]
  refine ⟨35497380197085319882615607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23664920131390213255077071 35497380197085319882615607)
  ·
    refine ⟨53246070295627979823923411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35497380197085319882615607 53246070295627979823923411)
    ·
      refine ⟨79869105443441969735885117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53246070295627979823923411 79869105443441969735885117)
      ·
        refine ⟨29950914541290738650956919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79869105443441969735885117 29950914541290738650956919)
        ·
          refine ⟨44926371811936107976435379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29950914541290738650956919 44926371811936107976435379)
          ·
            refine ⟨67389557717904161964653069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44926371811936107976435379 67389557717904161964653069)
            ·
              refine ⟨25271084144214060736744901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67389557717904161964653069 25271084144214060736744901)
              ·
                refine ⟨4738328277040136388139669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25271084144214060736744901 4738328277040136388139669)
                ·
                  refine ⟨222109137986256393194047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4738328277040136388139669 222109137986256393194047)
                  ·
                    rfl

theorem cell21_973251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 6].length) (baseStart_973251 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_973251 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_973251 prefixEnd_973251 := by exact prefixLift 973251
  have htrace : WordTrace (prefixWord ++ tailWord_973251) baseStart_973251 baseEnd_973251 := by
    simpa [prefixWord, tailWord_973251, baseEnd_973251] using wordTrace_append hprefix tailTrace_973251
  have hstable : (prefixWord ++ tailWord_973251).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973251).length < 2 ^ (prefixWord ++ tailWord_973251).sum := by decide
  have hdescent : baseEnd_973251 < baseStart_973251 := by decide
  rcases family_descends (prefixWord ++ tailWord_973251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973468 : List Nat := [2, 2, 3, 2, 2, 3, 2, 5]
def baseStart_973468 : Nat := 118140960795 + 973468 * 2 ^ 59
def prefixEnd_973468 : Nat := 4983230072969 + 3 ^ 40 * 973468 * 2
def baseEnd_973468 : Nat := 74052886780904079358979

theorem tailTrace_973468 : CollatzResearch.WordTrace tailWord_973468 prefixEnd_973468 74052886780904079358979 := by
  unfold tailWord_973468
  simp only [CollatzResearch.WordTrace]
  refine ⟨17752647418649582971632529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23670196558199443962176705 17752647418649582971632529)
  ·
    refine ⟨13314485563987187228724397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17752647418649582971632529 13314485563987187228724397)
    ·
      refine ⟨4992932086495195210771649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13314485563987187228724397 4992932086495195210771649)
      ·
        refine ⟨3744699064871396408078737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4992932086495195210771649 3744699064871396408078737)
        ·
          refine ⟨2808524298653547306059053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3744699064871396408078737 2808524298653547306059053)
          ·
            refine ⟨1053196611995080239772145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2808524298653547306059053 1053196611995080239772145)
            ·
              refine ⟨789897458996310179829109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1053196611995080239772145 789897458996310179829109)
              ·
                refine ⟨74052886780904079358979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 789897458996310179829109 74052886780904079358979)
                ·
                  rfl

theorem cell21_973468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 5].length) (baseStart_973468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_973468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_973468 prefixEnd_973468 := by exact prefixLift 973468
  have htrace : WordTrace (prefixWord ++ tailWord_973468) baseStart_973468 baseEnd_973468 := by
    simpa [prefixWord, tailWord_973468, baseEnd_973468] using wordTrace_append hprefix tailTrace_973468
  have hstable : (prefixWord ++ tailWord_973468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973468).length < 2 ^ (prefixWord ++ tailWord_973468).sum := by decide
  have hdescent : baseEnd_973468 < baseStart_973468 := by decide
  rcases family_descends (prefixWord ++ tailWord_973468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973572 : List Nat := [2, 3, 2, 2, 1, 1, 1, 5, 4]
def baseStart_973572 : Nat := 118140960795 + 973572 * 2 ^ 59
def prefixEnd_973572 : Nat := 4983230072969 + 3 ^ 40 * 973572 * 2
def baseEnd_973572 : Nat := 222182394559631168343391

theorem tailTrace_973572 : CollatzResearch.WordTrace tailWord_973572 prefixEnd_973572 222182394559631168343391 := by
  unfold tailWord_973572
  simp only [CollatzResearch.WordTrace]
  refine ⟨17754544014461195852525485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23672725352614927803367313 17754544014461195852525485)
  ·
    refine ⟨6657954005422948444697057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17754544014461195852525485 6657954005422948444697057)
    ·
      refine ⟨4993465504067211333522793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6657954005422948444697057 4993465504067211333522793)
      ·
        refine ⟨3745099128050408500142095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4993465504067211333522793 3745099128050408500142095)
        ·
          refine ⟨5617648692075612750213143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3745099128050408500142095 5617648692075612750213143)
          ·
            refine ⟨8426473038113419125319715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5617648692075612750213143 8426473038113419125319715)
            ·
              refine ⟨12639709557170128687979573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8426473038113419125319715 12639709557170128687979573)
              ·
                refine ⟨1184972770984699564498085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12639709557170128687979573 1184972770984699564498085)
                ·
                  refine ⟨222182394559631168343391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1184972770984699564498085 222182394559631168343391)
                  ·
                    rfl

theorem cell21_973572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_973572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_973572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_973572 prefixEnd_973572 := by exact prefixLift 973572
  have htrace : WordTrace (prefixWord ++ tailWord_973572) baseStart_973572 baseEnd_973572 := by
    simpa [prefixWord, tailWord_973572, baseEnd_973572] using wordTrace_append hprefix tailTrace_973572
  have hstable : (prefixWord ++ tailWord_973572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973572).length < 2 ^ (prefixWord ++ tailWord_973572).sum := by decide
  have hdescent : baseEnd_973572 < baseStart_973572 := by decide
  rcases family_descends (prefixWord ++ tailWord_973572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973617 : List Nat := [1, 2, 2, 3, 2, 1, 4, 1, 5]
def baseStart_973617 : Nat := 118140960795 + 973617 * 2 ^ 59
def prefixEnd_973617 : Nat := 4983230072969 + 3 ^ 40 * 973617 * 2
def baseEnd_973617 : Nat := 222192664172721090093299

theorem tailTrace_973617 : CollatzResearch.WordTrace tailWord_973617 prefixEnd_973617 222192664172721090093299 := by
  unfold tailWord_973617
  simp only [CollatzResearch.WordTrace]
  refine ⟨35510729313759364390439105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23673819542506242926959403 35510729313759364390439105)
  ·
    refine ⟨26633046985319523292829329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35510729313759364390439105 26633046985319523292829329)
    ·
      refine ⟨19974785238989642469621997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26633046985319523292829329 19974785238989642469621997)
      ·
        refine ⟨7490544464621115926108249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19974785238989642469621997 7490544464621115926108249)
        ·
          refine ⟨5617908348465836944581187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7490544464621115926108249 5617908348465836944581187)
          ·
            refine ⟨8426862522698755416871781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5617908348465836944581187 8426862522698755416871781)
            ·
              refine ⟨1580036723006016640663459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8426862522698755416871781 1580036723006016640663459)
              ·
                refine ⟨2370055084509024960995189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1580036723006016640663459 2370055084509024960995189)
                ·
                  refine ⟨222192664172721090093299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2370055084509024960995189 222192664172721090093299)
                  ·
                    rfl

theorem cell21_973617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 5].length) (baseStart_973617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_973617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_973617 prefixEnd_973617 := by exact prefixLift 973617
  have htrace : WordTrace (prefixWord ++ tailWord_973617) baseStart_973617 baseEnd_973617 := by
    simpa [prefixWord, tailWord_973617, baseEnd_973617] using wordTrace_append hprefix tailTrace_973617
  have hstable : (prefixWord ++ tailWord_973617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973617).length < 2 ^ (prefixWord ++ tailWord_973617).sum := by decide
  have hdescent : baseEnd_973617 < baseStart_973617 := by decide
  rcases family_descends (prefixWord ++ tailWord_973617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973727 : List Nat := [1, 1, 2, 5, 2, 1, 4, 2, 3]
def baseStart_973727 : Nat := 118140960795 + 973727 * 2 ^ 59
def prefixEnd_973727 : Nat := 4983230072969 + 3 ^ 40 * 973727 * 2
def baseEnd_973727 : Nat := 222217767671385343259741

theorem tailTrace_973727 : CollatzResearch.WordTrace tailWord_973727 prefixEnd_973727 222217767671385343259741 := by
  unfold tailWord_973727
  simp only [CollatzResearch.WordTrace]
  refine ⟨35514741343360853176943435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23676494228907235451295623 35514741343360853176943435)
  ·
    refine ⟨53272112015041279765415153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35514741343360853176943435 53272112015041279765415153)
    ·
      refine ⟨39954084011280959824061365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53272112015041279765415153 39954084011280959824061365)
      ·
        refine ⟨3745695376057589983505753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39954084011280959824061365 3745695376057589983505753)
        ·
          refine ⟨2809271532043192487629315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3745695376057589983505753 2809271532043192487629315)
          ·
            refine ⟨4213907298064788731443973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2809271532043192487629315 4213907298064788731443973)
            ·
              refine ⟨790107618387147887145745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4213907298064788731443973 790107618387147887145745)
              ·
                refine ⟨592580713790360915359309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 790107618387147887145745 592580713790360915359309)
                ·
                  refine ⟨222217767671385343259741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 592580713790360915359309 222217767671385343259741)
                  ·
                    rfl

theorem cell21_973727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 2, 3].length) (baseStart_973727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_973727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_973727 prefixEnd_973727 := by exact prefixLift 973727
  have htrace : WordTrace (prefixWord ++ tailWord_973727) baseStart_973727 baseEnd_973727 := by
    simpa [prefixWord, tailWord_973727, baseEnd_973727] using wordTrace_append hprefix tailTrace_973727
  have hstable : (prefixWord ++ tailWord_973727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973727).length < 2 ^ (prefixWord ++ tailWord_973727).sum := by decide
  have hdescent : baseEnd_973727 < baseStart_973727 := by decide
  rcases family_descends (prefixWord ++ tailWord_973727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973752 : List Nat := [2, 1, 2, 1, 2, 4, 1, 1, 7]
def baseStart_973752 : Nat := 118140960795 + 973752 * 2 ^ 59
def prefixEnd_973752 : Nat := 4983230072969 + 3 ^ 40 * 973752 * 2
def baseEnd_973752 : Nat := 222223473011990855343023

theorem tailTrace_973752 : CollatzResearch.WordTrace tailWord_973752 prefixEnd_973752 222223473011990855343023 := by
  unfold tailWord_973752
  simp only [CollatzResearch.WordTrace]
  refine ⟨17757826584135141223301755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23677102112180188297735673 17757826584135141223301755)
  ·
    refine ⟨26636739876202711834952633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17757826584135141223301755 26636739876202711834952633)
    ·
      refine ⟨19977554907152033876214475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26636739876202711834952633 19977554907152033876214475)
      ·
        refine ⟨29966332360728050814321713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19977554907152033876214475 29966332360728050814321713)
        ·
          refine ⟨22474749270546038110741285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29966332360728050814321713 22474749270546038110741285)
          ·
            refine ⟨4214015488227382145763991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22474749270546038110741285 4214015488227382145763991)
            ·
              refine ⟨6321023232341073218645987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4214015488227382145763991 6321023232341073218645987)
              ·
                refine ⟨9481534848511609827968981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6321023232341073218645987 9481534848511609827968981)
                ·
                  refine ⟨222223473011990855343023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9481534848511609827968981 222223473011990855343023)
                  ·
                    rfl

theorem cell21_973752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 7].length) (baseStart_973752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_973752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_973752 prefixEnd_973752 := by exact prefixLift 973752
  have htrace : WordTrace (prefixWord ++ tailWord_973752) baseStart_973752 baseEnd_973752 := by
    simpa [prefixWord, tailWord_973752, baseEnd_973752] using wordTrace_append hprefix tailTrace_973752
  have hstable : (prefixWord ++ tailWord_973752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973752).length < 2 ^ (prefixWord ++ tailWord_973752).sum := by decide
  have hdescent : baseEnd_973752 < baseStart_973752 := by decide
  rcases family_descends (prefixWord ++ tailWord_973752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973783 : List Nat := [1, 1, 3, 2, 1, 1, 2, 6, 4]
def baseStart_973783 : Nat := 118140960795 + 973783 * 2 ^ 59
def prefixEnd_973783 : Nat := 4983230072969 + 3 ^ 40 * 973783 * 2
def baseEnd_973783 : Nat := 222230547634341690326293

theorem tailTrace_973783 : CollatzResearch.WordTrace tailWord_973783 prefixEnd_973783 222230547634341690326293 := by
  unfold tailWord_973783
  simp only [CollatzResearch.WordTrace]
  refine ⟨35516783831157974740982003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23677855887438649827321335 35516783831157974740982003)
  ·
    refine ⟨53275175746736962111473005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35516783831157974740982003 53275175746736962111473005)
    ·
      refine ⟨19978190905026360791802377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53275175746736962111473005 19978190905026360791802377)
      ·
        refine ⟨14983643178769770593851783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19978190905026360791802377 14983643178769770593851783)
        ·
          refine ⟨22475464768154655890777675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14983643178769770593851783 22475464768154655890777675)
          ·
            refine ⟨33713197152231983836166513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22475464768154655890777675 33713197152231983836166513)
            ·
              refine ⟨25284897864173987877124885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33713197152231983836166513 25284897864173987877124885)
              ·
                refine ⟨1185229587383155681740229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25284897864173987877124885 1185229587383155681740229)
                ·
                  refine ⟨222230547634341690326293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1185229587383155681740229 222230547634341690326293)
                  ·
                    rfl

theorem cell21_973783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6, 4].length) (baseStart_973783 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_973783 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_973783 prefixEnd_973783 := by exact prefixLift 973783
  have htrace : WordTrace (prefixWord ++ tailWord_973783) baseStart_973783 baseEnd_973783 := by
    simpa [prefixWord, tailWord_973783, baseEnd_973783] using wordTrace_append hprefix tailTrace_973783
  have hstable : (prefixWord ++ tailWord_973783).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973783).length < 2 ^ (prefixWord ++ tailWord_973783).sum := by decide
  have hdescent : baseEnd_973783 < baseStart_973783 := by decide
  rcases family_descends (prefixWord ++ tailWord_973783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973786 : List Nat := [3, 1, 1, 2, 4, 1, 2, 4, 3]
def baseStart_973786 : Nat := 118140960795 + 973786 * 2 ^ 59
def prefixEnd_973786 : Nat := 4983230072969 + 3 ^ 40 * 973786 * 2
def baseEnd_973786 : Nat := 222231232275214351776287

theorem tailTrace_973786 : CollatzResearch.WordTrace tailWord_973786 prefixEnd_973786 222231232275214351776287 := by
  unfold tailWord_973786
  simp only [CollatzResearch.WordTrace]
  refine ⟨8879223312536776563335303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23677928833431404168894141 8879223312536776563335303)
  ·
    refine ⟨13318834968805164845002955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8879223312536776563335303 13318834968805164845002955)
    ·
      refine ⟨19978252453207747267504433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13318834968805164845002955 19978252453207747267504433)
      ·
        refine ⟨14983689339905810450628325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19978252453207747267504433 14983689339905810450628325)
        ·
          refine ⟨2809441751232339459492811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14983689339905810450628325 2809441751232339459492811)
          ·
            refine ⟨4214162626848509189239217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2809441751232339459492811 4214162626848509189239217)
            ·
              refine ⟨3160621970136381891929413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4214162626848509189239217 3160621970136381891929413)
              ·
                refine ⟨592616619400571604736765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3160621970136381891929413 592616619400571604736765)
                ·
                  refine ⟨222231232275214351776287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 592616619400571604736765 222231232275214351776287)
                  ·
                    rfl

theorem cell21_973786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 4, 3].length) (baseStart_973786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_973786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_973786 prefixEnd_973786 := by exact prefixLift 973786
  have htrace : WordTrace (prefixWord ++ tailWord_973786) baseStart_973786 baseEnd_973786 := by
    simpa [prefixWord, tailWord_973786, baseEnd_973786] using wordTrace_append hprefix tailTrace_973786
  have hstable : (prefixWord ++ tailWord_973786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973786).length < 2 ^ (prefixWord ++ tailWord_973786).sum := by decide
  have hdescent : baseEnd_973786 < baseStart_973786 := by decide
  rcases family_descends (prefixWord ++ tailWord_973786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973845 : List Nat := [1, 3, 2, 1, 4, 1, 3, 1, 5]
def baseStart_973845 : Nat := 118140960795 + 973845 * 2 ^ 59
def prefixEnd_973845 : Nat := 4983230072969 + 3 ^ 40 * 973845 * 2
def baseEnd_973845 : Nat := 222244696879043360292833

theorem tailTrace_973845 : CollatzResearch.WordTrace tailWord_973845 prefixEnd_973845 222244696879043360292833 := by
  unfold tailWord_973845
  simp only [CollatzResearch.WordTrace]
  refine ⟨35519045156933359329738989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23679363437955572886492659 35519045156933359329738989)
  ·
    refine ⟨13319641933850009748652121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35519045156933359329738989 13319641933850009748652121)
    ·
      refine ⟨9989731450387507311489091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13319641933850009748652121 9989731450387507311489091)
      ·
        refine ⟨14984597175581260967233637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9989731450387507311489091 14984597175581260967233637)
        ·
          refine ⟨2809611970421486431356307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14984597175581260967233637 2809611970421486431356307)
          ·
            refine ⟨4214417955632229647034461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2809611970421486431356307 4214417955632229647034461)
            ·
              refine ⟨1580406733362086117637923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4214417955632229647034461 1580406733362086117637923)
              ·
                refine ⟨2370610100043129176456885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1580406733362086117637923 2370610100043129176456885)
                ·
                  refine ⟨222244696879043360292833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2370610100043129176456885 222244696879043360292833)
                  ·
                    rfl

theorem cell21_973845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 5].length) (baseStart_973845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_973845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_973845 prefixEnd_973845 := by exact prefixLift 973845
  have htrace : WordTrace (prefixWord ++ tailWord_973845) baseStart_973845 baseEnd_973845 := by
    simpa [prefixWord, tailWord_973845, baseEnd_973845] using wordTrace_append hprefix tailTrace_973845
  have hstable : (prefixWord ++ tailWord_973845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973845).length < 2 ^ (prefixWord ++ tailWord_973845).sum := by decide
  have hdescent : baseEnd_973845 < baseStart_973845 := by decide
  rcases family_descends (prefixWord ++ tailWord_973845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973873 : List Nat := [1, 2, 2, 3, 1, 2, 1, 9]
def baseStart_973873 : Nat := 118140960795 + 973873 * 2 ^ 59
def prefixEnd_973873 : Nat := 4983230072969 + 3 ^ 40 * 973873 * 2
def baseEnd_973873 : Nat := 74083695620173844608703

theorem tailTrace_973873 : CollatzResearch.WordTrace tailWord_973873 prefixEnd_973873 74083695620173844608703 := by
  unfold tailWord_973873
  simp only [CollatzResearch.WordTrace]
  refine ⟨35520066400831920111758273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23680044267221280074505515 35520066400831920111758273)
  ·
    refine ⟨26640049800623940083818705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35520066400831920111758273 26640049800623940083818705)
    ·
      refine ⟨19980037350467955062864029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26640049800623940083818705 19980037350467955062864029)
      ·
        refine ⟨7492514006425483148574011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19980037350467955062864029 7492514006425483148574011)
        ·
          refine ⟨11238771009638224722861017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7492514006425483148574011 11238771009638224722861017)
          ·
            refine ⟨8429078257228668542145763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11238771009638224722861017 8429078257228668542145763)
            ·
              refine ⟨12643617385843002813218645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8429078257228668542145763 12643617385843002813218645)
              ·
                refine ⟨74083695620173844608703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12643617385843002813218645 74083695620173844608703)
                ·
                  rfl

theorem cell21_973873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 9].length) (baseStart_973873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_973873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_973873 prefixEnd_973873 := by exact prefixLift 973873
  have htrace : WordTrace (prefixWord ++ tailWord_973873) baseStart_973873 baseEnd_973873 := by
    simpa [prefixWord, tailWord_973873, baseEnd_973873] using wordTrace_append hprefix tailTrace_973873
  have hstable : (prefixWord ++ tailWord_973873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973873).length < 2 ^ (prefixWord ++ tailWord_973873).sum := by decide
  have hdescent : baseEnd_973873 < baseStart_973873 := by decide
  rcases family_descends (prefixWord ++ tailWord_973873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973938 : List Nat := [3, 2, 1, 2, 2, 1, 4, 3, 3]
def baseStart_973938 : Nat := 118140960795 + 973938 * 2 ^ 59
def prefixEnd_973938 : Nat := 4983230072969 + 3 ^ 40 * 973938 * 2
def baseEnd_973938 : Nat := 222265920746095865242643

theorem tailTrace_973938 : CollatzResearch.WordTrace tailWord_973938 prefixEnd_973938 222265920746095865242643 := by
  unfold tailWord_973938
  simp only [CollatzResearch.WordTrace]
  refine ⟨8880609286399109053218617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23681624763730957475249645 8880609286399109053218617)
  ·
    refine ⟨6660456964799331789913963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8880609286399109053218617 6660456964799331789913963)
    ·
      refine ⟨9990685447198997684870945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6660456964799331789913963 9990685447198997684870945)
      ·
        refine ⟨7493014085399248263653209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9990685447198997684870945 7493014085399248263653209)
        ·
          refine ⟨5619760564049436197739907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7493014085399248263653209 5619760564049436197739907)
          ·
            refine ⟨8429640846074154296609861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5619760564049436197739907 8429640846074154296609861)
            ·
              refine ⟨1580557658638903930614349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8429640846074154296609861 1580557658638903930614349)
              ·
                refine ⟨592709121989588973980381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1580557658638903930614349 592709121989588973980381)
                ·
                  refine ⟨222265920746095865242643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 592709121989588973980381 222265920746095865242643)
                  ·
                    rfl

theorem cell21_973938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 3, 3].length) (baseStart_973938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_973938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_973938 prefixEnd_973938 := by exact prefixLift 973938
  have htrace : WordTrace (prefixWord ++ tailWord_973938) baseStart_973938 baseEnd_973938 := by
    simpa [prefixWord, tailWord_973938, baseEnd_973938] using wordTrace_append hprefix tailTrace_973938
  have hstable : (prefixWord ++ tailWord_973938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973938).length < 2 ^ (prefixWord ++ tailWord_973938).sum := by decide
  have hdescent : baseEnd_973938 < baseStart_973938 := by decide
  rcases family_descends (prefixWord ++ tailWord_973938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973949 : List Nat := [1, 4, 1, 1, 3, 1, 10]
def baseStart_973949 : Nat := 118140960795 + 973949 * 2 ^ 59
def prefixEnd_973949 : Nat := 4983230072969 + 3 ^ 40 * 973949 * 2
def baseEnd_973949 : Nat := 24696492343995810062143

theorem tailTrace_973949 : CollatzResearch.WordTrace tailWord_973949 prefixEnd_973949 24696492343995810062143 := by
  unfold tailWord_973949
  simp only [CollatzResearch.WordTrace]
  refine ⟨35522838348556585091524901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23681892232371056727683267 35522838348556585091524901)
  ·
    refine ⟨6660532190354359704660919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35522838348556585091524901 6660532190354359704660919)
    ·
      refine ⟨9990798285531539556991379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6660532190354359704660919 9990798285531539556991379)
      ·
        refine ⟨14986197428297309335487069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9990798285531539556991379 14986197428297309335487069)
        ·
          refine ⟨5619824035611491000807651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14986197428297309335487069 5619824035611491000807651)
          ·
            refine ⟨8429736053417236501211477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5619824035611491000807651 8429736053417236501211477)
            ·
              refine ⟨24696492343995810062143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8429736053417236501211477 24696492343995810062143)
              ·
                rfl

theorem cell21_973949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 10].length) (baseStart_973949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_973949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_973949 prefixEnd_973949 := by exact prefixLift 973949
  have htrace : WordTrace (prefixWord ++ tailWord_973949) baseStart_973949 baseEnd_973949 := by
    simpa [prefixWord, tailWord_973949, baseEnd_973949] using wordTrace_append hprefix tailTrace_973949
  have hstable : (prefixWord ++ tailWord_973949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973949).length < 2 ^ (prefixWord ++ tailWord_973949).sum := by decide
  have hdescent : baseEnd_973949 < baseStart_973949 := by decide
  rcases family_descends (prefixWord ++ tailWord_973949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974014 : List Nat := [4, 2, 1, 1, 3, 3, 1, 1, 5]
def baseStart_974014 : Nat := 118140960795 + 974014 * 2 ^ 59
def prefixEnd_974014 : Nat := 4983230072969 + 3 ^ 40 * 974014 * 2
def baseEnd_974014 : Nat := 222283264981536621975821

theorem tailTrace_974014 : CollatzResearch.WordTrace tailWord_974014 prefixEnd_974014 222283264981536621975821 := by
  unfold tailWord_974014
  simp only [CollatzResearch.WordTrace]
  refine ⟨4440651136665137649080137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23683472728880734128427397 4440651136665137649080137)
  ·
    refine ⟨3330488352498853236810103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4440651136665137649080137 3330488352498853236810103)
    ·
      refine ⟨4995732528748279855215155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3330488352498853236810103 4995732528748279855215155)
      ·
        refine ⟨7493598793122419782822733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4995732528748279855215155 7493598793122419782822733)
        ·
          refine ⟨2810099547420907418558525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7493598793122419782822733 2810099547420907418558525)
          ·
            refine ⟨1053787330282840281959447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2810099547420907418558525 1053787330282840281959447)
            ·
              refine ⟨1580680995424260422939171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1053787330282840281959447 1580680995424260422939171)
              ·
                refine ⟨2371021493136390634408757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1580680995424260422939171 2371021493136390634408757)
                ·
                  refine ⟨222283264981536621975821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2371021493136390634408757 222283264981536621975821)
                  ·
                    rfl

theorem cell21_974014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_974014 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_974014 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_974014 prefixEnd_974014 := by exact prefixLift 974014
  have htrace : WordTrace (prefixWord ++ tailWord_974014) baseStart_974014 baseEnd_974014 := by
    simpa [prefixWord, tailWord_974014, baseEnd_974014] using wordTrace_append hprefix tailTrace_974014
  have hstable : (prefixWord ++ tailWord_974014).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974014).length < 2 ^ (prefixWord ++ tailWord_974014).sum := by decide
  have hdescent : baseEnd_974014 < baseStart_974014 := by decide
  rcases family_descends (prefixWord ++ tailWord_974014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974073 : List Nat := [1, 2, 1, 3, 1, 1, 5, 4, 3]
def baseStart_974073 : Nat := 118140960795 + 974073 * 2 ^ 59
def prefixEnd_974073 : Nat := 4983230072969 + 3 ^ 40 * 974073 * 2
def baseEnd_974073 : Nat := 222296729585365630492367

theorem tailTrace_974073 : CollatzResearch.WordTrace tailWord_974073 prefixEnd_974073 222296729585365630492367 := by
  unfold tailWord_974073
  simp only [CollatzResearch.WordTrace]
  refine ⟨35527361000107354269038873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23684907333404902846025915 35527361000107354269038873)
  ·
    refine ⟨26645520750080515701779155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35527361000107354269038873 26645520750080515701779155)
    ·
      refine ⟨39968281125120773552668733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26645520750080515701779155 39968281125120773552668733)
      ·
        refine ⟨14988105421920290082250775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39968281125120773552668733 14988105421920290082250775)
        ·
          refine ⟨22482158132880435123376163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14988105421920290082250775 22482158132880435123376163)
          ·
            refine ⟨33723237199320652685064245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22482158132880435123376163 33723237199320652685064245)
            ·
              refine ⟨3161553487436311189224773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33723237199320652685064245 3161553487436311189224773)
              ·
                refine ⟨592791278894308347979645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3161553487436311189224773 592791278894308347979645)
                ·
                  refine ⟨222296729585365630492367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 592791278894308347979645 222296729585365630492367)
                  ·
                    rfl

theorem cell21_974073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 4, 3].length) (baseStart_974073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_974073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_974073 prefixEnd_974073 := by exact prefixLift 974073
  have htrace : WordTrace (prefixWord ++ tailWord_974073) baseStart_974073 baseEnd_974073 := by
    simpa [prefixWord, tailWord_974073, baseEnd_974073] using wordTrace_append hprefix tailTrace_974073
  have hstable : (prefixWord ++ tailWord_974073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974073).length < 2 ^ (prefixWord ++ tailWord_974073).sum := by decide
  have hdescent : baseEnd_974073 < baseStart_974073 := by decide
  rcases family_descends (prefixWord ++ tailWord_974073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974183 : List Nat := [1, 1, 5, 1, 4, 1, 3, 2, 3]
def baseStart_974183 : Nat := 118140960795 + 974183 * 2 ^ 59
def prefixEnd_974183 : Nat := 4983230072969 + 3 ^ 40 * 974183 * 2
def baseEnd_974183 : Nat := 222321833084029883658809

theorem tailTrace_974183 : CollatzResearch.WordTrace tailWord_974183 prefixEnd_974183 222321833084029883658809 := by
  unfold tailWord_974183
  simp only [CollatzResearch.WordTrace]
  refine ⟨35531373029708843055543203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23687582019805895370362135 35531373029708843055543203)
  ·
    refine ⟨53297059544563264583314805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35531373029708843055543203 53297059544563264583314805)
    ·
      refine ⟨4996599332302806054685763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53297059544563264583314805 4996599332302806054685763)
      ·
        refine ⟨7494898998454209082028645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4996599332302806054685763 7494898998454209082028645)
        ·
          refine ⟨1405293562210164202880371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7494898998454209082028645 1405293562210164202880371)
          ·
            refine ⟨2107940343315246304320557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1405293562210164202880371 2107940343315246304320557)
            ·
              refine ⟨790477628743217364120209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2107940343315246304320557 790477628743217364120209)
              ·
                refine ⟨592858221557413023090157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 790477628743217364120209 592858221557413023090157)
                ·
                  refine ⟨222321833084029883658809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 592858221557413023090157 222321833084029883658809)
                  ·
                    rfl

theorem cell21_974183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 2, 3].length) (baseStart_974183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_974183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_974183 prefixEnd_974183 := by exact prefixLift 974183
  have htrace : WordTrace (prefixWord ++ tailWord_974183) baseStart_974183 baseEnd_974183 := by
    simpa [prefixWord, tailWord_974183, baseEnd_974183] using wordTrace_append hprefix tailTrace_974183
  have hstable : (prefixWord ++ tailWord_974183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974183).length < 2 ^ (prefixWord ++ tailWord_974183).sum := by decide
  have hdescent : baseEnd_974183 < baseStart_974183 := by decide
  rcases family_descends (prefixWord ++ tailWord_974183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974239 : List Nat := [1, 1, 2, 5, 1, 2, 1, 4, 4]
def baseStart_974239 : Nat := 118140960795 + 974239 * 2 ^ 59
def prefixEnd_974239 : Nat := 4983230072969 + 3 ^ 40 * 974239 * 2
def baseEnd_974239 : Nat := 222334613046986230725361

theorem tailTrace_974239 : CollatzResearch.WordTrace tailWord_974239 prefixEnd_974239 222334613046986230725361 := by
  unfold tailWord_974239
  simp only [CollatzResearch.WordTrace]
  refine ⟨35533415517505964619581771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23688943678337309746387847 35533415517505964619581771)
  ·
    refine ⟨53300123276258946929372657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35533415517505964619581771 53300123276258946929372657)
    ·
      refine ⟨39975092457194210197029493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53300123276258946929372657 39975092457194210197029493)
      ·
        refine ⟨3747664917861957205971515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39975092457194210197029493 3747664917861957205971515)
        ·
          refine ⟨5621497376792935808957273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3747664917861957205971515 5621497376792935808957273)
          ·
            refine ⟨4216123032594701856717955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5621497376792935808957273 4216123032594701856717955)
            ·
              refine ⟨6324184548892052785076933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4216123032594701856717955 6324184548892052785076933)
              ·
                refine ⟨1185784602917259897201925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6324184548892052785076933 1185784602917259897201925)
                ·
                  refine ⟨222334613046986230725361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1185784602917259897201925 222334613046986230725361)
                  ·
                    rfl

theorem cell21_974239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4, 4].length) (baseStart_974239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_974239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_974239 prefixEnd_974239 := by exact prefixLift 974239
  have htrace : WordTrace (prefixWord ++ tailWord_974239) baseStart_974239 baseEnd_974239 := by
    simpa [prefixWord, tailWord_974239, baseEnd_974239] using wordTrace_append hprefix tailTrace_974239
  have hstable : (prefixWord ++ tailWord_974239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974239).length < 2 ^ (prefixWord ++ tailWord_974239).sum := by decide
  have hdescent : baseEnd_974239 < baseStart_974239 := by decide
  rcases family_descends (prefixWord ++ tailWord_974239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974242 : List Nat := [3, 3, 1, 2, 1, 3, 1, 4, 3]
def baseStart_974242 : Nat := 118140960795 + 974242 * 2 ^ 59
def prefixEnd_974242 : Nat := 4983230072969 + 3 ^ 40 * 974242 * 2
def baseEnd_974242 : Nat := 222335297687858892175355

theorem tailTrace_974242 : CollatzResearch.WordTrace tailWord_974242 prefixEnd_974242 222335297687858892175355 := by
  unfold tailWord_974242
  simp only [CollatzResearch.WordTrace]
  refine ⟨8883381234123774032985245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23689016624330064087960653 8883381234123774032985245)
  ·
    refine ⟨3331267962796415262369467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8883381234123774032985245 3331267962796415262369467)
    ·
      refine ⟨4996901944194622893554201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3331267962796415262369467 4996901944194622893554201)
      ·
        refine ⟨3747676458145967170165651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4996901944194622893554201 3747676458145967170165651)
        ·
          refine ⟨5621514687218950755248477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3747676458145967170165651 5621514687218950755248477)
          ·
            refine ⟨2108068007707106533218179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5621514687218950755248477 2108068007707106533218179)
            ·
              refine ⟨3162102011560659799827269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2108068007707106533218179 3162102011560659799827269)
              ·
                refine ⟨592894127167623712467613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3162102011560659799827269 592894127167623712467613)
                ·
                  refine ⟨222335297687858892175355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 592894127167623712467613 222335297687858892175355)
                  ·
                    rfl

theorem cell21_974242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_974242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_974242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_974242 prefixEnd_974242 := by exact prefixLift 974242
  have htrace : WordTrace (prefixWord ++ tailWord_974242) baseStart_974242 baseEnd_974242 := by
    simpa [prefixWord, tailWord_974242, baseEnd_974242] using wordTrace_append hprefix tailTrace_974242
  have hstable : (prefixWord ++ tailWord_974242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974242).length < 2 ^ (prefixWord ++ tailWord_974242).sum := by decide
  have hdescent : baseEnd_974242 < baseStart_974242 := by decide
  rcases family_descends (prefixWord ++ tailWord_974242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974301 : List Nat := [1, 4, 3, 1, 1, 3, 2, 1, 5]
def baseStart_974301 : Nat := 118140960795 + 974301 * 2 ^ 59
def prefixEnd_974301 : Nat := 4983230072969 + 3 ^ 40 * 974301 * 2
def baseEnd_974301 : Nat := 222348762291687900691901

theorem tailTrace_974301 : CollatzResearch.WordTrace tailWord_974301 prefixEnd_974301 222348762291687900691901 := by
  unfold tailWord_974301
  simp only [CollatzResearch.WordTrace]
  refine ⟨35535676843281349208338757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23690451228854232805559171 35535676843281349208338757)
  ·
    refine ⟨6662939408115252976563517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35535676843281349208338757 6662939408115252976563517)
    ·
      refine ⟨2498602278043219866211319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6662939408115252976563517 2498602278043219866211319)
      ·
        refine ⟨3747903417064829799316979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2498602278043219866211319 3747903417064829799316979)
        ·
          refine ⟨5621855125597244698975469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3747903417064829799316979 5621855125597244698975469)
          ·
            refine ⟨2108195672098966762115801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5621855125597244698975469 2108195672098966762115801)
            ·
              refine ⟨1581146754074225071586851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2108195672098966762115801 1581146754074225071586851)
              ·
                refine ⟨2371720131111337607380277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1581146754074225071586851 2371720131111337607380277)
                ·
                  refine ⟨222348762291687900691901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2371720131111337607380277 222348762291687900691901)
                  ·
                    rfl

theorem cell21_974301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_974301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_974301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_974301 prefixEnd_974301 := by exact prefixLift 974301
  have htrace : WordTrace (prefixWord ++ tailWord_974301) baseStart_974301 baseEnd_974301 := by
    simpa [prefixWord, tailWord_974301, baseEnd_974301] using wordTrace_append hprefix tailTrace_974301
  have hstable : (prefixWord ++ tailWord_974301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974301).length < 2 ^ (prefixWord ++ tailWord_974301).sum := by decide
  have hdescent : baseEnd_974301 < baseStart_974301 := by decide
  rcases family_descends (prefixWord ++ tailWord_974301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974436 : List Nat := [2, 3, 1, 1, 2, 4, 1, 2, 5]
def baseStart_974436 : Nat := 118140960795 + 974436 * 2 ^ 59
def prefixEnd_974436 : Nat := 4983230072969 + 3 ^ 40 * 974436 * 2
def baseEnd_974436 : Nat := 222379571130957665941625

theorem tailTrace_974436 : CollatzResearch.WordTrace tailWord_974436 prefixEnd_974436 222379571130957665941625 := by
  unfold tailWord_974436
  simp only [CollatzResearch.WordTrace]
  refine ⟨17770300348896133632251581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23693733798528178176335441 17770300348896133632251581)
  ·
    refine ⟨6663862630836050112094343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17770300348896133632251581 6663862630836050112094343)
    ·
      refine ⟨9995793946254075168141515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6663862630836050112094343 9995793946254075168141515)
      ·
        refine ⟨14993690919381112752212273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9995793946254075168141515 14993690919381112752212273)
        ·
          refine ⟨11245268189535834564159205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14993690919381112752212273 11245268189535834564159205)
          ·
            refine ⟨2108487785537968980779851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11245268189535834564159205 2108487785537968980779851)
            ·
              refine ⟨3162731678306953471169777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2108487785537968980779851 3162731678306953471169777)
              ·
                refine ⟨2372048758730215103377333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3162731678306953471169777 2372048758730215103377333)
                ·
                  refine ⟨222379571130957665941625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2372048758730215103377333 222379571130957665941625)
                  ·
                    rfl

theorem cell21_974436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_974436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_974436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_974436 prefixEnd_974436 := by exact prefixLift 974436
  have htrace : WordTrace (prefixWord ++ tailWord_974436) baseStart_974436 baseEnd_974436 := by
    simpa [prefixWord, tailWord_974436, baseEnd_974436] using wordTrace_append hprefix tailTrace_974436
  have hstable : (prefixWord ++ tailWord_974436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974436).length < 2 ^ (prefixWord ++ tailWord_974436).sum := by decide
  have hdescent : baseEnd_974436 < baseStart_974436 := by decide
  rcases family_descends (prefixWord ++ tailWord_974436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974464 : List Nat := [2, 1, 1, 2, 1, 4, 10]
def baseStart_974464 : Nat := 118140960795 + 974464 * 2 ^ 59
def prefixEnd_974464 : Nat := 4983230072969 + 3 ^ 40 * 974464 * 2
def baseEnd_974464 : Nat := 24709551234715093274989

theorem tailTrace_974464 : CollatzResearch.WordTrace tailWord_974464 prefixEnd_974464 24709551234715093274989 := by
  unfold tailWord_974464
  simp only [CollatzResearch.WordTrace]
  refine ⟨17770810970845414023261223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23694414627793885364348297 17770810970845414023261223)
  ·
    refine ⟨26656216456268121034891835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17770810970845414023261223 26656216456268121034891835)
    ·
      refine ⟨39984324684402181552337753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26656216456268121034891835 39984324684402181552337753)
      ·
        refine ⟨29988243513301636164253315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39984324684402181552337753 29988243513301636164253315)
        ·
          refine ⟨44982365269952454246379973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29988243513301636164253315 44982365269952454246379973)
          ·
            refine ⟨8434193488116085171196245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44982365269952454246379973 8434193488116085171196245)
            ·
              refine ⟨24709551234715093274989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8434193488116085171196245 24709551234715093274989)
              ·
                rfl

theorem cell21_974464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 10].length) (baseStart_974464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_974464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_974464 prefixEnd_974464 := by exact prefixLift 974464
  have htrace : WordTrace (prefixWord ++ tailWord_974464) baseStart_974464 baseEnd_974464 := by
    simpa [prefixWord, tailWord_974464, baseEnd_974464] using wordTrace_append hprefix tailTrace_974464
  have hstable : (prefixWord ++ tailWord_974464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974464).length < 2 ^ (prefixWord ++ tailWord_974464).sum := by decide
  have hdescent : baseEnd_974464 < baseStart_974464 := by decide
  rcases family_descends (prefixWord ++ tailWord_974464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974580 : List Nat := [2, 6, 1, 1, 1, 1, 4, 2, 3]
def baseStart_974580 : Nat := 118140960795 + 974580 * 2 ^ 59
def prefixEnd_974580 : Nat := 4983230072969 + 3 ^ 40 * 974580 * 2
def baseEnd_974580 : Nat := 222412433892845415541331

theorem tailTrace_974580 : CollatzResearch.WordTrace tailWord_974580 prefixEnd_974580 222412433892845415541331 := by
  unfold tailWord_974580
  simp only [CollatzResearch.WordTrace]
  refine ⟨17772926404635289928872597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23697235206180386571830129 17772926404635289928872597)
  ·
    refine ⟨833105925217279215415903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17772926404635289928872597 833105925217279215415903)
    ·
      refine ⟨1249658887825918823123855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 833105925217279215415903 1249658887825918823123855)
      ·
        refine ⟨1874488331738878234685783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1249658887825918823123855 1874488331738878234685783)
        ·
          refine ⟨2811732497608317352028675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1874488331738878234685783 2811732497608317352028675)
          ·
            refine ⟨4217598746412476028043013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2811732497608317352028675 4217598746412476028043013)
            ·
              refine ⟨790799764952339255258065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4217598746412476028043013 790799764952339255258065)
              ·
                refine ⟨593099823714254441443549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 790799764952339255258065 593099823714254441443549)
                ·
                  refine ⟨222412433892845415541331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 593099823714254441443549 222412433892845415541331)
                  ·
                    rfl

theorem cell21_974580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_974580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_974580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_974580 prefixEnd_974580 := by exact prefixLift 974580
  have htrace : WordTrace (prefixWord ++ tailWord_974580) baseStart_974580 baseEnd_974580 := by
    simpa [prefixWord, tailWord_974580, baseEnd_974580] using wordTrace_append hprefix tailTrace_974580
  have hstable : (prefixWord ++ tailWord_974580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974580).length < 2 ^ (prefixWord ++ tailWord_974580).sum := by decide
  have hdescent : baseEnd_974580 < baseStart_974580 := by decide
  rcases family_descends (prefixWord ++ tailWord_974580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974616 : List Nat := [2, 1, 2, 3, 1, 1, 2, 9]
def baseStart_974616 : Nat := 118140960795 + 974616 * 2 ^ 59
def prefixEnd_974616 : Nat := 4983230072969 + 3 ^ 40 * 974616 * 2
def baseEnd_974616 : Nat := 74140216527772450980419

theorem tailTrace_974616 : CollatzResearch.WordTrace tailWord_974616 prefixEnd_974616 74140216527772450980419 := by
  unfold tailWord_974616
  simp only [CollatzResearch.WordTrace]
  refine ⟨17773582918570079003027851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23698110558093438670703801 17773582918570079003027851)
  ·
    refine ⟨26660374377855118504541777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17773582918570079003027851 26660374377855118504541777)
    ·
      refine ⟨19995280783391338878406333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26660374377855118504541777 19995280783391338878406333)
      ·
        refine ⟨7498230293771752079402375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19995280783391338878406333 7498230293771752079402375)
        ·
          refine ⟨11247345440657628119103563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7498230293771752079402375 11247345440657628119103563)
          ·
            refine ⟨16871018160986442178655345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11247345440657628119103563 16871018160986442178655345)
            ·
              refine ⟨12653263620739831633991509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16871018160986442178655345 12653263620739831633991509)
              ·
                refine ⟨74140216527772450980419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12653263620739831633991509 74140216527772450980419)
                ·
                  rfl

theorem cell21_974616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 9].length) (baseStart_974616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_974616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_974616 prefixEnd_974616 := by exact prefixLift 974616
  have htrace : WordTrace (prefixWord ++ tailWord_974616) baseStart_974616 baseEnd_974616 := by
    simpa [prefixWord, tailWord_974616, baseEnd_974616] using wordTrace_append hprefix tailTrace_974616
  have hstable : (prefixWord ++ tailWord_974616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974616).length < 2 ^ (prefixWord ++ tailWord_974616).sum := by decide
  have hdescent : baseEnd_974616 < baseStart_974616 := by decide
  rcases family_descends (prefixWord ++ tailWord_974616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974698 : List Nat := [3, 1, 3, 4, 1, 2, 1, 1, 5]
def baseStart_974698 : Nat := 118140960795 + 974698 * 2 ^ 59
def prefixEnd_974698 : Nat := 4983230072969 + 3 ^ 40 * 974698 * 2
def baseEnd_974698 : Nat := 222439363100503432574423

theorem tailTrace_974698 : CollatzResearch.WordTrace tailWord_974698 prefixEnd_974698 222439363100503432574423 := by
  unfold tailWord_974698
  simp only [CollatzResearch.WordTrace]
  refine ⟨8887539155710771502635187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23700104415228724007027165 8887539155710771502635187)
  ·
    refine ⟨13331308733566157253952781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8887539155710771502635187 13331308733566157253952781)
    ·
      refine ⟨4999240775087308970232293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13331308733566157253952781 4999240775087308970232293)
      ·
        refine ⟨937357645328870431918555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4999240775087308970232293 937357645328870431918555)
        ·
          refine ⟨1406036467993305647877833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 937357645328870431918555 1406036467993305647877833)
          ·
            refine ⟨1054527350994979235908375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1406036467993305647877833 1054527350994979235908375)
            ·
              refine ⟨1581791026492468853862563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1054527350994979235908375 1581791026492468853862563)
              ·
                refine ⟨2372686539738703280793845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1581791026492468853862563 2372686539738703280793845)
                ·
                  refine ⟨222439363100503432574423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2372686539738703280793845 222439363100503432574423)
                  ·
                    rfl

theorem cell21_974698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 5].length) (baseStart_974698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_974698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_974698 prefixEnd_974698 := by exact prefixLift 974698
  have htrace : WordTrace (prefixWord ++ tailWord_974698) baseStart_974698 baseEnd_974698 := by
    simpa [prefixWord, tailWord_974698, baseEnd_974698] using wordTrace_append hprefix tailTrace_974698
  have hstable : (prefixWord ++ tailWord_974698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974698).length < 2 ^ (prefixWord ++ tailWord_974698).sum := by decide
  have hdescent : baseEnd_974698 < baseStart_974698 := by decide
  rcases family_descends (prefixWord ++ tailWord_974698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974709 : List Nat := [1, 3, 4, 1, 1, 1, 4, 6]
def baseStart_974709 : Nat := 118140960795 + 974709 * 2 ^ 59
def prefixEnd_974709 : Nat := 4983230072969 + 3 ^ 40 * 974709 * 2
def baseEnd_974709 : Nat := 74147291150123285963689

theorem tailTrace_974709 : CollatzResearch.WordTrace tailWord_974709 prefixEnd_974709 74147291150123285963689 := by
  unfold tailWord_974709
  simp only [CollatzResearch.WordTrace]
  refine ⟨35550557825803234889191181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23700371883868823259460787 35550557825803234889191181)
  ·
    refine ⟨13331459184676213083446693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35550557825803234889191181 13331459184676213083446693)
    ·
      refine ⟨2499648597126789953146255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13331459184676213083446693 2499648597126789953146255)
      ·
        refine ⟨3749472895690184929719383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2499648597126789953146255 3749472895690184929719383)
        ·
          refine ⟨5624209343535277394579075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3749472895690184929719383 5624209343535277394579075)
          ·
            refine ⟨8436314015302916091868613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5624209343535277394579075 8436314015302916091868613)
            ·
              refine ⟨1581808877869296767225365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8436314015302916091868613 1581808877869296767225365)
              ·
                refine ⟨74147291150123285963689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1581808877869296767225365 74147291150123285963689)
                ·
                  rfl

theorem cell21_974709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 6].length) (baseStart_974709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_974709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_974709 prefixEnd_974709 := by exact prefixLift 974709
  have htrace : WordTrace (prefixWord ++ tailWord_974709) baseStart_974709 baseEnd_974709 := by
    simpa [prefixWord, tailWord_974709, baseEnd_974709] using wordTrace_append hprefix tailTrace_974709
  have hstable : (prefixWord ++ tailWord_974709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974709).length < 2 ^ (prefixWord ++ tailWord_974709).sum := by decide
  have hdescent : baseEnd_974709 < baseStart_974709 := by decide
  rcases family_descends (prefixWord ++ tailWord_974709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974737 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 8]
def baseStart_974737 : Nat := 118140960795 + 974737 * 2 ^ 59
def prefixEnd_974737 : Nat := 4983230072969 + 3 ^ 40 * 974737 * 2
def baseEnd_974737 : Nat := 222448263431848031424343

theorem tailTrace_974737 : CollatzResearch.WordTrace tailWord_974737 prefixEnd_974737 222448263431848031424343 := by
  unfold tailWord_974737
  simp only [CollatzResearch.WordTrace]
  refine ⟨35551579069701795671210465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23701052713134530447473643 35551579069701795671210465)
  ·
    refine ⟨26663684302276346753407849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35551579069701795671210465 26663684302276346753407849)
    ·
      refine ⟨19997763226707260065055887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26663684302276346753407849 19997763226707260065055887)
      ·
        refine ⟨29996644840060890097583831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19997763226707260065055887 29996644840060890097583831)
        ·
          refine ⟨44994967260091335146375747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29996644840060890097583831 44994967260091335146375747)
          ·
            refine ⟨67492450890137002719563621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44994967260091335146375747 67492450890137002719563621)
            ·
              refine ⟨12654834541900688009918179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67492450890137002719563621 12654834541900688009918179)
              ·
                refine ⟨18982251812851032014877269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12654834541900688009918179 18982251812851032014877269)
                ·
                  refine ⟨222448263431848031424343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18982251812851032014877269 222448263431848031424343)
                  ·
                    rfl

theorem cell21_974737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 8].length) (baseStart_974737 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_974737 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_974737 prefixEnd_974737 := by exact prefixLift 974737
  have htrace : WordTrace (prefixWord ++ tailWord_974737) baseStart_974737 baseEnd_974737 := by
    simpa [prefixWord, tailWord_974737, baseEnd_974737] using wordTrace_append hprefix tailTrace_974737
  have hstable : (prefixWord ++ tailWord_974737).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974737).length < 2 ^ (prefixWord ++ tailWord_974737).sum := by decide
  have hdescent : baseEnd_974737 < baseStart_974737 := by decide
  rcases family_descends (prefixWord ++ tailWord_974737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974760 : List Nat := [2, 1, 6, 2, 2, 1, 1, 6]
def baseStart_974760 : Nat := 118140960795 + 974760 * 2 ^ 59
def prefixEnd_974760 : Nat := 4983230072969 + 3 ^ 40 * 974760 * 2
def baseEnd_974760 : Nat := 74151170781735034180321

theorem tailTrace_974760 : CollatzResearch.WordTrace tailWord_974760 prefixEnd_974760 74151170781735034180321 := by
  unfold tailWord_974760
  simp only [CollatzResearch.WordTrace]
  refine ⟨17776208974309235299648867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23701611965745647066198489 17776208974309235299648867)
  ·
    refine ⟨26664313461463852949473301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17776208974309235299648867 26664313461463852949473301)
    ·
      refine ⟨1249889693506118107006561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26664313461463852949473301 1249889693506118107006561)
      ·
        refine ⟨937417270129588580254921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1249889693506118107006561 937417270129588580254921)
        ·
          refine ⟨703062952597191435191191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 937417270129588580254921 703062952597191435191191)
          ·
            refine ⟨1054594428895787152786787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 703062952597191435191191 1054594428895787152786787)
            ·
              refine ⟨1581891643343680729180181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1054594428895787152786787 1581891643343680729180181)
              ·
                refine ⟨74151170781735034180321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1581891643343680729180181 74151170781735034180321)
                ·
                  rfl

theorem cell21_974760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 6].length) (baseStart_974760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_974760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_974760 prefixEnd_974760 := by exact prefixLift 974760
  have htrace : WordTrace (prefixWord ++ tailWord_974760) baseStart_974760 baseEnd_974760 := by
    simpa [prefixWord, tailWord_974760, baseEnd_974760] using wordTrace_append hprefix tailTrace_974760
  have hstable : (prefixWord ++ tailWord_974760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974760).length < 2 ^ (prefixWord ++ tailWord_974760).sum := by decide
  have hdescent : baseEnd_974760 < baseStart_974760 := by decide
  rcases family_descends (prefixWord ++ tailWord_974760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974844 : List Nat := [2, 2, 2, 1, 2, 2, 3, 7]
def baseStart_974844 : Nat := 118140960795 + 974844 * 2 ^ 59
def prefixEnd_974844 : Nat := 4983230072969 + 3 ^ 40 * 974844 * 2
def baseEnd_974844 : Nat := 74157560763213207713597

theorem tailTrace_974844 : CollatzResearch.WordTrace tailWord_974844 prefixEnd_974844 74157560763213207713597 := by
  unfold tailWord_974844
  simp only [CollatzResearch.WordTrace]
  refine ⟨17777740840157076472677793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23703654453542768630237057 17777740840157076472677793)
  ·
    refine ⟨13333305630117807354508345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17777740840157076472677793 13333305630117807354508345)
    ·
      refine ⟨9999979222588355515881259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13333305630117807354508345 9999979222588355515881259)
      ·
        refine ⟨14999968833882533273821889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9999979222588355515881259 14999968833882533273821889)
        ·
          refine ⟨11249976625411899955366417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14999968833882533273821889 11249976625411899955366417)
          ·
            refine ⟨8437482469058924966524813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11249976625411899955366417 8437482469058924966524813)
            ·
              refine ⟨3164055925897096862446805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8437482469058924966524813 3164055925897096862446805)
              ·
                refine ⟨74157560763213207713597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3164055925897096862446805 74157560763213207713597)
                ·
                  rfl

theorem cell21_974844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 7].length) (baseStart_974844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_974844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_974844 prefixEnd_974844 := by exact prefixLift 974844
  have htrace : WordTrace (prefixWord ++ tailWord_974844) baseStart_974844 baseEnd_974844 := by
    simpa [prefixWord, tailWord_974844, baseEnd_974844] using wordTrace_append hprefix tailTrace_974844
  have hstable : (prefixWord ++ tailWord_974844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974844).length < 2 ^ (prefixWord ++ tailWord_974844).sum := by decide
  have hdescent : baseEnd_974844 < baseStart_974844 := by decide
  rcases family_descends (prefixWord ++ tailWord_974844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974881 : List Nat := [1, 2, 3, 2, 5, 1, 2, 1, 4]
def baseStart_974881 : Nat := 118140960795 + 974881 * 2 ^ 59
def prefixEnd_974881 : Nat := 4983230072969 + 3 ^ 40 * 974881 * 2
def baseEnd_974881 : Nat := 222481126193735781024049

theorem tailTrace_974881 : CollatzResearch.WordTrace tailWord_974881 prefixEnd_974881 222481126193735781024049 := by
  unfold tailWord_974881
  simp only [CollatzResearch.WordTrace]
  refine ⟨35556831181180108264452497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23704554120786738842968331 35556831181180108264452497)
  ·
    refine ⟨26667623385885081198339373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35556831181180108264452497 26667623385885081198339373)
    ·
      refine ⟨10000358769706905449377265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26667623385885081198339373 10000358769706905449377265)
      ·
        refine ⟨7500269077280179087032949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10000358769706905449377265 7500269077280179087032949)
        ·
          refine ⟨703150225995016789409339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7500269077280179087032949 703150225995016789409339)
          ·
            refine ⟨1054725338992525184114009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 703150225995016789409339 1054725338992525184114009)
            ·
              refine ⟨791044004244393888085507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1054725338992525184114009 791044004244393888085507)
              ·
                refine ⟨1186566006366590832128261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 791044004244393888085507 1186566006366590832128261)
                ·
                  refine ⟨222481126193735781024049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1186566006366590832128261 222481126193735781024049)
                  ·
                    rfl

theorem cell21_974881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 1, 4].length) (baseStart_974881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_974881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_974881 prefixEnd_974881 := by exact prefixLift 974881
  have htrace : WordTrace (prefixWord ++ tailWord_974881) baseStart_974881 baseEnd_974881 := by
    simpa [prefixWord, tailWord_974881, baseEnd_974881] using wordTrace_append hprefix tailTrace_974881
  have hstable : (prefixWord ++ tailWord_974881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974881).length < 2 ^ (prefixWord ++ tailWord_974881).sum := by decide
  have hdescent : baseEnd_974881 < baseStart_974881 := by decide
  rcases family_descends (prefixWord ++ tailWord_974881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974926 : List Nat := [4, 1, 1, 1, 1, 6, 2, 2, 3]
def baseStart_974926 : Nat := 118140960795 + 974926 * 2 ^ 59
def prefixEnd_974926 : Nat := 4983230072969 + 3 ^ 40 * 974926 * 2
def baseEnd_974926 : Nat := 222491395806825702773957

theorem tailTrace_974926 : CollatzResearch.WordTrace tailWord_974926 prefixEnd_974926 222491395806825702773957 := by
  unfold tailWord_974926
  simp only [CollatzResearch.WordTrace]
  refine ⟨4444809058252135118730079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23705648310678053966560421 4444809058252135118730079)
  ·
    refine ⟨6667213587378202678095119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4444809058252135118730079 6667213587378202678095119)
    ·
      refine ⟨10000820381067304017142679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6667213587378202678095119 10000820381067304017142679)
      ·
        refine ⟨15001230571600956025714019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10000820381067304017142679 15001230571600956025714019)
        ·
          refine ⟨22501845857401434038571029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15001230571600956025714019 22501845857401434038571029)
          ·
            refine ⟨1054774024565692220558017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22501845857401434038571029 1054774024565692220558017)
            ·
              refine ⟨791080518424269165418513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1054774024565692220558017 791080518424269165418513)
              ·
                refine ⟨593310388818201874063885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 791080518424269165418513 593310388818201874063885)
                ·
                  refine ⟨222491395806825702773957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 593310388818201874063885 222491395806825702773957)
                  ·
                    rfl

theorem cell21_974926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 2, 3].length) (baseStart_974926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_974926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_974926 prefixEnd_974926 := by exact prefixLift 974926
  have htrace : WordTrace (prefixWord ++ tailWord_974926) baseStart_974926 baseEnd_974926 := by
    simpa [prefixWord, tailWord_974926, baseEnd_974926] using wordTrace_append hprefix tailTrace_974926
  have hstable : (prefixWord ++ tailWord_974926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974926).length < 2 ^ (prefixWord ++ tailWord_974926).sum := by decide
  have hdescent : baseEnd_974926 < baseStart_974926 := by decide
  rcases family_descends (prefixWord ++ tailWord_974926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974951 : List Nat := [1, 1, 5, 1, 1, 2, 3, 2, 5]
def baseStart_974951 : Nat := 118140960795 + 974951 * 2 ^ 59
def prefixEnd_974951 : Nat := 4983230072969 + 3 ^ 40 * 974951 * 2
def baseEnd_974951 : Nat := 222497101147431214857239

theorem tailTrace_974951 : CollatzResearch.WordTrace tailWord_974951 prefixEnd_974951 222497101147431214857239 := by
  unfold tailWord_974951
  simp only [CollatzResearch.WordTrace]
  refine ⟨35559384290926510219500707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23706256193951006813000471 35559384290926510219500707)
  ·
    refine ⟨53339076436389765329251061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35559384290926510219500707 53339076436389765329251061)
    ·
      refine ⟨5000538415911540499617287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53339076436389765329251061 5000538415911540499617287)
      ·
        refine ⟨7500807623867310749425931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5000538415911540499617287 7500807623867310749425931)
        ·
          refine ⟨11251211435800966124138897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7500807623867310749425931 11251211435800966124138897)
          ·
            refine ⟨8438408576850724593104173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11251211435800966124138897 8438408576850724593104173)
            ·
              refine ⟨3164403216319021722414065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8438408576850724593104173 3164403216319021722414065)
              ·
                refine ⟨2373302412239266291810549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3164403216319021722414065 2373302412239266291810549)
                ·
                  refine ⟨222497101147431214857239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2373302412239266291810549 222497101147431214857239)
                  ·
                    rfl

theorem cell21_974951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 5].length) (baseStart_974951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_974951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_974951 prefixEnd_974951 := by exact prefixLift 974951
  have htrace : WordTrace (prefixWord ++ tailWord_974951) baseStart_974951 baseEnd_974951 := by
    simpa [prefixWord, tailWord_974951, baseEnd_974951] using wordTrace_append hprefix tailTrace_974951
  have hstable : (prefixWord ++ tailWord_974951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974951).length < 2 ^ (prefixWord ++ tailWord_974951).sum := by decide
  have hdescent : baseEnd_974951 < baseStart_974951 := by decide
  rcases family_descends (prefixWord ++ tailWord_974951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974954 : List Nat := [3, 1, 3, 2, 3, 1, 3, 5]
def baseStart_974954 : Nat := 118140960795 + 974954 * 2 ^ 59
def prefixEnd_974954 : Nat := 4983230072969 + 3 ^ 40 * 974954 * 2
def baseEnd_974954 : Nat := 74165928596101292102411

theorem tailTrace_974954 : CollatzResearch.WordTrace tailWord_974954 prefixEnd_974954 74165928596101292102411 := by
  unfold tailWord_974954
  simp only [CollatzResearch.WordTrace]
  refine ⟨8889873427478910432964979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23706329139943761154573277 8889873427478910432964979)
  ·
    refine ⟨13334810141218365649447469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8889873427478910432964979 13334810141218365649447469)
    ·
      refine ⟨5000553802956887118542801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13334810141218365649447469 5000553802956887118542801)
      ·
        refine ⟨3750415352217665338907101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5000553802956887118542801 3750415352217665338907101)
        ·
          refine ⟨1406405757081624502090163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3750415352217665338907101 1406405757081624502090163)
          ·
            refine ⟨2109608635622436753135245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1406405757081624502090163 2109608635622436753135245)
            ·
              refine ⟨791103238358413782425717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2109608635622436753135245 791103238358413782425717)
              ·
                refine ⟨74165928596101292102411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 791103238358413782425717 74165928596101292102411)
                ·
                  rfl

theorem cell21_974954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 5].length) (baseStart_974954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_974954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_974954 prefixEnd_974954 := by exact prefixLift 974954
  have htrace : WordTrace (prefixWord ++ tailWord_974954) baseStart_974954 baseEnd_974954 := by
    simpa [prefixWord, tailWord_974954, baseEnd_974954] using wordTrace_append hprefix tailTrace_974954
  have hstable : (prefixWord ++ tailWord_974954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974954).length < 2 ^ (prefixWord ++ tailWord_974954).sum := by decide
  have hdescent : baseEnd_974954 < baseStart_974954 := by decide
  rcases family_descends (prefixWord ++ tailWord_974954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975044 : List Nat := [2, 3, 3, 1, 2, 1, 3, 1, 5]
def baseStart_975044 : Nat := 118140960795 + 975044 * 2 ^ 59
def prefixEnd_975044 : Nat := 4983230072969 + 3 ^ 40 * 975044 * 2
def baseEnd_975044 : Nat := 222518325014483719807049

theorem tailTrace_975044 : CollatzResearch.WordTrace tailWord_975044 prefixEnd_975044 222518325014483719807049 := by
  unfold tailWord_975044
  simp only [CollatzResearch.WordTrace]
  refine ⟨17781388139794793551318093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23708517519726391401757457 17781388139794793551318093)
  ·
    refine ⟨6668020552423047581744285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17781388139794793551318093 6668020552423047581744285)
    ·
      refine ⟨2500507707158642843154107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6668020552423047581744285 2500507707158642843154107)
      ·
        refine ⟨3750761560737964264731161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2500507707158642843154107 3750761560737964264731161)
        ·
          refine ⟨2813071170553473198548371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3750761560737964264731161 2813071170553473198548371)
          ·
            refine ⟨4219606755830209797822557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2813071170553473198548371 4219606755830209797822557)
            ·
              refine ⟨1582352533436328674183459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4219606755830209797822557 1582352533436328674183459)
              ·
                refine ⟨2373528800154493011275189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1582352533436328674183459 2373528800154493011275189)
                ·
                  refine ⟨222518325014483719807049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2373528800154493011275189 222518325014483719807049)
                  ·
                    rfl

theorem cell21_975044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_975044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_975044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_975044 prefixEnd_975044 := by exact prefixLift 975044
  have htrace : WordTrace (prefixWord ++ tailWord_975044) baseStart_975044 baseEnd_975044 := by
    simpa [prefixWord, tailWord_975044, baseEnd_975044] using wordTrace_append hprefix tailTrace_975044
  have hstable : (prefixWord ++ tailWord_975044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975044).length < 2 ^ (prefixWord ++ tailWord_975044).sum := by decide
  have hdescent : baseEnd_975044 < baseStart_975044 := by decide
  rcases family_descends (prefixWord ++ tailWord_975044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975106 : List Nat := [3, 4, 1, 1, 2, 3, 1, 6]
def baseStart_975106 : Nat := 118140960795 + 975106 * 2 ^ 59
def prefixEnd_975106 : Nat := 4983230072969 + 3 ^ 40 * 975106 * 2
def baseEnd_975106 : Nat := 74177491419728463257863

theorem tailTrace_975106 : CollatzResearch.WordTrace tailWord_975106 prefixEnd_975106 74177491419728463257863 := by
  unfold tailWord_975106
  simp only [CollatzResearch.WordTrace]
  refine ⟨8891259401341242922848293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23710025070243314460928781 8891259401341242922848293)
  ·
    refine ⟨1667111137751483048034055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8891259401341242922848293 1667111137751483048034055)
    ·
      refine ⟨2500666706627224572051083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1667111137751483048034055 2500666706627224572051083)
      ·
        refine ⟨3751000059940836858076625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2500666706627224572051083 3751000059940836858076625)
        ·
          refine ⟨2813250044955627643557469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3751000059940836858076625 2813250044955627643557469)
          ·
            refine ⟨1054968766858360366334051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2813250044955627643557469 1054968766858360366334051)
            ·
              refine ⟨1582453150287540549501077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1054968766858360366334051 1582453150287540549501077)
              ·
                refine ⟨74177491419728463257863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1582453150287540549501077 74177491419728463257863)
                ·
                  rfl

theorem cell21_975106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 6].length) (baseStart_975106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_975106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_975106 prefixEnd_975106 := by exact prefixLift 975106
  have htrace : WordTrace (prefixWord ++ tailWord_975106) baseStart_975106 baseEnd_975106 := by
    simpa [prefixWord, tailWord_975106, baseEnd_975106] using wordTrace_append hprefix tailTrace_975106
  have hstable : (prefixWord ++ tailWord_975106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975106).length < 2 ^ (prefixWord ++ tailWord_975106).sum := by decide
  have hdescent : baseEnd_975106 < baseStart_975106 := by decide
  rcases family_descends (prefixWord ++ tailWord_975106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975131 : List Nat := [1, 1, 1, 1, 1, 1, 6, 9]
def baseStart_975131 : Nat := 118140960795 + 975131 * 2 ^ 59
def prefixEnd_975131 : Nat := 4983230072969 + 3 ^ 40 * 975131 * 2
def baseEnd_975131 : Nat := 74179393199930300618957

theorem tailTrace_975131 : CollatzResearch.WordTrace tailWord_975131 prefixEnd_975131 74179393199930300618957 := by
  unfold tailWord_975131
  simp only [CollatzResearch.WordTrace]
  refine ⟨35565949430274400961053247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23710632953516267307368831 35565949430274400961053247)
  ·
    refine ⟨53348924145411601441579871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35565949430274400961053247 53348924145411601441579871)
    ·
      refine ⟨80023386218117402162369807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53348924145411601441579871 80023386218117402162369807)
      ·
        refine ⟨120035079327176103243554711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80023386218117402162369807 120035079327176103243554711)
        ·
          refine ⟨180052618990764154865332067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120035079327176103243554711 180052618990764154865332067)
          ·
            refine ⟨270078928486146232297998101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180052618990764154865332067 270078928486146232297998101)
            ·
              refine ⟨12659949772788104638968661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 270078928486146232297998101 12659949772788104638968661)
              ·
                refine ⟨74179393199930300618957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12659949772788104638968661 74179393199930300618957)
                ·
                  rfl

theorem cell21_975131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 9].length) (baseStart_975131 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_975131 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_975131 prefixEnd_975131 := by exact prefixLift 975131
  have htrace : WordTrace (prefixWord ++ tailWord_975131) baseStart_975131 baseEnd_975131 := by
    simpa [prefixWord, tailWord_975131, baseEnd_975131] using wordTrace_append hprefix tailTrace_975131
  have hstable : (prefixWord ++ tailWord_975131).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975131).length < 2 ^ (prefixWord ++ tailWord_975131).sum := by decide
  have hdescent : baseEnd_975131 < baseStart_975131 := by decide
  rcases family_descends (prefixWord ++ tailWord_975131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975210 : List Nat := [3, 1, 3, 3, 1, 1, 2, 1, 6]
def baseStart_975210 : Nat := 118140960795 + 975210 * 2 ^ 59
def prefixEnd_975210 : Nat := 4983230072969 + 3 ^ 40 * 975210 * 2
def baseEnd_975210 : Nat := 222556208476104320040043

theorem tailTrace_975210 : CollatzResearch.WordTrace tailWord_975210 prefixEnd_975210 222556208476104320040043 := by
  unfold tailWord_975210
  simp only [CollatzResearch.WordTrace]
  refine ⟨8892207699247049363294771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23712553864658798302119389 8892207699247049363294771)
  ·
    refine ⟨13338311548870574044942157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8892207699247049363294771 13338311548870574044942157)
    ·
      refine ⟨5001866830826465266853309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13338311548870574044942157 5001866830826465266853309)
      ·
        refine ⟨1875700061559924475069991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5001866830826465266853309 1875700061559924475069991)
        ·
          refine ⟨2813550092339886712604987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1875700061559924475069991 2813550092339886712604987)
          ·
            refine ⟨4220325138509830068907481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2813550092339886712604987 4220325138509830068907481)
            ·
              refine ⟨3165243853882372551680611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4220325138509830068907481 3165243853882372551680611)
              ·
                refine ⟨4747865780823558827520917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3165243853882372551680611 4747865780823558827520917)
                ·
                  refine ⟨222556208476104320040043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4747865780823558827520917 222556208476104320040043)
                  ·
                    rfl

theorem cell21_975210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 6].length) (baseStart_975210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_975210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_975210 prefixEnd_975210 := by exact prefixLift 975210
  have htrace : WordTrace (prefixWord ++ tailWord_975210) baseStart_975210 baseEnd_975210 := by
    simpa [prefixWord, tailWord_975210, baseEnd_975210] using wordTrace_append hprefix tailTrace_975210
  have hstable : (prefixWord ++ tailWord_975210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975210).length < 2 ^ (prefixWord ++ tailWord_975210).sum := by decide
  have hdescent : baseEnd_975210 < baseStart_975210 := by decide
  rcases family_descends (prefixWord ++ tailWord_975210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975213 : List Nat := [1, 5, 1, 1, 1, 2, 5, 2, 3]
def baseStart_975213 : Nat := 118140960795 + 975213 * 2 ^ 59
def prefixEnd_975213 : Nat := 4983230072969 + 3 ^ 40 * 975213 * 2
def baseEnd_975213 : Nat := 222556893116976981490037

theorem tailTrace_975213 : CollatzResearch.WordTrace tailWord_975213 prefixEnd_975213 222556893116976981490037 := by
  unfold tailWord_975213
  simp only [CollatzResearch.WordTrace]
  refine ⟨35568940215977328965538293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23712626810651552643692195 35568940215977328965538293)
  ·
    refine ⟨3334588145247874590519215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35568940215977328965538293 3334588145247874590519215)
    ·
      refine ⟨5001882217871811885778823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3334588145247874590519215 5001882217871811885778823)
      ·
        refine ⟨7502823326807717828668235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5001882217871811885778823 7502823326807717828668235)
        ·
          refine ⟨11254234990211576743002353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7502823326807717828668235 11254234990211576743002353)
          ·
            refine ⟨8440676242658682557251765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11254234990211576743002353 8440676242658682557251765)
            ·
              refine ⟨791313397749251489742353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8440676242658682557251765 791313397749251489742353)
              ·
                refine ⟨593485048311938617306765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 791313397749251489742353 593485048311938617306765)
                ·
                  refine ⟨222556893116976981490037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 593485048311938617306765 222556893116976981490037)
                  ·
                    rfl

theorem cell21_975213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_975213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_975213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_975213 prefixEnd_975213 := by exact prefixLift 975213
  have htrace : WordTrace (prefixWord ++ tailWord_975213) baseStart_975213 baseEnd_975213 := by
    simpa [prefixWord, tailWord_975213, baseEnd_975213] using wordTrace_append hprefix tailTrace_975213
  have hstable : (prefixWord ++ tailWord_975213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975213).length < 2 ^ (prefixWord ++ tailWord_975213).sum := by decide
  have hdescent : baseEnd_975213 < baseStart_975213 := by decide
  rcases family_descends (prefixWord ++ tailWord_975213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975227 : List Nat := [1, 1, 1, 1, 1, 9, 2, 1, 4]
def baseStart_975227 : Nat := 118140960795 + 975227 * 2 ^ 59
def prefixEnd_975227 : Nat := 4983230072969 + 3 ^ 40 * 975227 * 2
def baseEnd_975227 : Nat := 222560088107716068256675

theorem tailTrace_975227 : CollatzResearch.WordTrace tailWord_975227 prefixEnd_975227 222560088107716068256675 := by
  unfold tailWord_975227
  simp only [CollatzResearch.WordTrace]
  refine ⟨35569450837926609356547935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23712967225284406237698623 35569450837926609356547935)
  ·
    refine ⟨53354176256889914034821903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35569450837926609356547935 53354176256889914034821903)
    ·
      refine ⟨80031264385334871052232855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53354176256889914034821903 80031264385334871052232855)
      ·
        refine ⟨120046896578002306578349283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80031264385334871052232855 120046896578002306578349283)
        ·
          refine ⟨180070344867003459867523925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120046896578002306578349283 180070344867003459867523925)
          ·
            refine ⟨1055099676955098397661273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 180070344867003459867523925 1055099676955098397661273)
            ·
              refine ⟨791324757716323798245955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1055099676955098397661273 791324757716323798245955)
              ·
                refine ⟨1186987136574485697368933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 791324757716323798245955 1186987136574485697368933)
                ·
                  refine ⟨222560088107716068256675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1186987136574485697368933 222560088107716068256675)
                  ·
                    rfl

theorem cell21_975227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 1, 4].length) (baseStart_975227 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_975227 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_975227 prefixEnd_975227 := by exact prefixLift 975227
  have htrace : WordTrace (prefixWord ++ tailWord_975227) baseStart_975227 baseEnd_975227 := by
    simpa [prefixWord, tailWord_975227, baseEnd_975227] using wordTrace_append hprefix tailTrace_975227
  have hstable : (prefixWord ++ tailWord_975227).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975227).length < 2 ^ (prefixWord ++ tailWord_975227).sum := by decide
  have hdescent : baseEnd_975227 < baseStart_975227 := by decide
  rcases family_descends (prefixWord ++ tailWord_975227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975359 : List Nat := [1, 1, 2, 2, 1, 2, 5, 7]
def baseStart_975359 : Nat := 118140960795 + 975359 * 2 ^ 59
def prefixEnd_975359 : Nat := 4983230072969 + 3 ^ 40 * 975359 * 2
def baseEnd_975359 : Nat := 74196737435371057352135

theorem tailTrace_975359 : CollatzResearch.WordTrace tailWord_975359 prefixEnd_975359 74196737435371057352135 := by
  unfold tailWord_975359
  simp only [CollatzResearch.WordTrace]
  refine ⟨35574265273448395900353131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23716176848965597266902087 35574265273448395900353131)
  ·
    refine ⟨53361397910172593850529697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35574265273448395900353131 53361397910172593850529697)
    ·
      refine ⟨40021048432629445387897273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53361397910172593850529697 40021048432629445387897273)
      ·
        refine ⟨30015786324472084040922955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40021048432629445387897273 30015786324472084040922955)
        ·
          refine ⟨45023679486708126061384433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30015786324472084040922955 45023679486708126061384433)
          ·
            refine ⟨33767759615031094546038325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45023679486708126061384433 33767759615031094546038325)
            ·
              refine ⟨3165727463909165113691093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33767759615031094546038325 3165727463909165113691093)
              ·
                refine ⟨74196737435371057352135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3165727463909165113691093 74196737435371057352135)
                ·
                  rfl

theorem cell21_975359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 7].length) (baseStart_975359 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_975359 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_975359 prefixEnd_975359 := by exact prefixLift 975359
  have htrace : WordTrace (prefixWord ++ tailWord_975359) baseStart_975359 baseEnd_975359 := by
    simpa [prefixWord, tailWord_975359, baseEnd_975359] using wordTrace_append hprefix tailTrace_975359
  have hstable : (prefixWord ++ tailWord_975359).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975359).length < 2 ^ (prefixWord ++ tailWord_975359).sum := by decide
  have hdescent : baseEnd_975359 < baseStart_975359 := by decide
  rcases family_descends (prefixWord ++ tailWord_975359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975441 : List Nat := [1, 2, 2, 1, 3, 5, 2, 2, 3]
def baseStart_975441 : Nat := 118140960795 + 975441 * 2 ^ 59
def prefixEnd_975441 : Nat := 4983230072969 + 3 ^ 40 * 975441 * 2
def baseEnd_975441 : Nat := 222608925823299251689571

theorem tailTrace_975441 : CollatzResearch.WordTrace tailWord_975441 prefixEnd_975441 222608925823299251689571 := by
  unfold tailWord_975441
  simp only [CollatzResearch.WordTrace]
  refine ⟨35577256059151323904838177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23718170706100882603225451 35577256059151323904838177)
  ·
    refine ⟨26682942044363492928628633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35577256059151323904838177 26682942044363492928628633)
    ·
      refine ⟨20012206533272619696471475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26682942044363492928628633 20012206533272619696471475)
      ·
        refine ⟨30018309799908929544707213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20012206533272619696471475 30018309799908929544707213)
        ·
          refine ⟨11256866174965848579265205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30018309799908929544707213 11256866174965848579265205)
          ·
            refine ⟨1055331203903048304306113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11256866174965848579265205 1055331203903048304306113)
            ·
              refine ⟨791498402927286228229585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1055331203903048304306113 791498402927286228229585)
              ·
                refine ⟨593623802195464671172189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 791498402927286228229585 593623802195464671172189)
                ·
                  refine ⟨222608925823299251689571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 593623802195464671172189 222608925823299251689571)
                  ·
                    rfl

theorem cell21_975441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 2, 3].length) (baseStart_975441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_975441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_975441 prefixEnd_975441 := by exact prefixLift 975441
  have htrace : WordTrace (prefixWord ++ tailWord_975441) baseStart_975441 baseEnd_975441 := by
    simpa [prefixWord, tailWord_975441, baseEnd_975441] using wordTrace_append hprefix tailTrace_975441
  have hstable : (prefixWord ++ tailWord_975441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975441).length < 2 ^ (prefixWord ++ tailWord_975441).sum := by decide
  have hdescent : baseEnd_975441 < baseStart_975441 := by decide
  rcases family_descends (prefixWord ++ tailWord_975441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975469 : List Nat := [1, 5, 1, 1, 3, 2, 3, 5]
def baseStart_975469 : Nat := 118140960795 + 975469 * 2 ^ 59
def prefixEnd_975469 : Nat := 4983230072969 + 3 ^ 40 * 975469 * 2
def baseEnd_975469 : Nat := 74205105268259141740949

theorem tailTrace_975469 : CollatzResearch.WordTrace tailWord_975469 prefixEnd_975469 74205105268259141740949 := by
  unfold tailWord_975469
  simp only [CollatzResearch.WordTrace]
  refine ⟨35578277303049884686857461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23718851535366589791238307 35578277303049884686857461)
  ·
    refine ⟨3335463497160926689392887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35578277303049884686857461 3335463497160926689392887)
    ·
      refine ⟨5003195245741390034089331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3335463497160926689392887 5003195245741390034089331)
      ·
        refine ⟨7504792868612085051133997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5003195245741390034089331 7504792868612085051133997)
        ·
          refine ⟨2814297325729531894175249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7504792868612085051133997 2814297325729531894175249)
          ·
            refine ⟨2110722994297148920631437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2814297325729531894175249 2110722994297148920631437)
            ·
              refine ⟨791521122861430845236789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2110722994297148920631437 791521122861430845236789)
              ·
                refine ⟨74205105268259141740949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 791521122861430845236789 74205105268259141740949)
                ·
                  rfl

theorem cell21_975469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 5].length) (baseStart_975469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_975469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_975469 prefixEnd_975469 := by exact prefixLift 975469
  have htrace : WordTrace (prefixWord ++ tailWord_975469) baseStart_975469 baseEnd_975469 := by
    simpa [prefixWord, tailWord_975469, baseEnd_975469] using wordTrace_append hprefix tailTrace_975469
  have hstable : (prefixWord ++ tailWord_975469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975469).length < 2 ^ (prefixWord ++ tailWord_975469).sum := by decide
  have hdescent : baseEnd_975469 < baseStart_975469 := by decide
  rcases family_descends (prefixWord ++ tailWord_975469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975480 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 8]
def baseStart_975480 : Nat := 118140960795 + 975480 * 2 ^ 59
def prefixEnd_975480 : Nat := 4983230072969 + 3 ^ 40 * 975480 * 2
def baseEnd_975480 : Nat := 222617826154643850539491

theorem tailTrace_975480 : CollatzResearch.WordTrace tailWord_975480 prefixEnd_975480 222617826154643850539491 := by
  unfold tailWord_975480
  simp only [CollatzResearch.WordTrace]
  refine ⟨17789339253005016782753947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23719119004006689043671929 17789339253005016782753947)
  ·
    refine ⟨26684008879507525174130921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17789339253005016782753947 26684008879507525174130921)
    ·
      refine ⟨20013006659630643880598191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26684008879507525174130921 20013006659630643880598191)
      ·
        refine ⟨30019509989445965820897287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20013006659630643880598191 30019509989445965820897287)
        ·
          refine ⟨45029264984168948731345931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30019509989445965820897287 45029264984168948731345931)
          ·
            refine ⟨67543897476253423097018897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45029264984168948731345931 67543897476253423097018897)
            ·
              refine ⟨50657923107190067322764173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67543897476253423097018897 50657923107190067322764173)
              ·
                refine ⟨18996721165196275246036565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50657923107190067322764173 18996721165196275246036565)
                ·
                  refine ⟨222617826154643850539491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18996721165196275246036565 222617826154643850539491)
                  ·
                    rfl

theorem cell21_975480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 8].length) (baseStart_975480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_975480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_975480 prefixEnd_975480 := by exact prefixLift 975480
  have htrace : WordTrace (prefixWord ++ tailWord_975480) baseStart_975480 baseEnd_975480 := by
    simpa [prefixWord, tailWord_975480, baseEnd_975480] using wordTrace_append hprefix tailTrace_975480
  have hstable : (prefixWord ++ tailWord_975480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975480).length < 2 ^ (prefixWord ++ tailWord_975480).sum := by decide
  have hdescent : baseEnd_975480 < baseStart_975480 := by decide
  rcases family_descends (prefixWord ++ tailWord_975480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975511 : List Nat := [1, 1, 3, 3, 2, 1, 2, 8]
def baseStart_975511 : Nat := 118140960795 + 975511 * 2 ^ 59
def prefixEnd_975511 : Nat := 4983230072969 + 3 ^ 40 * 975511 * 2
def baseEnd_975511 : Nat := 74208300258998228507587

theorem tailTrace_975511 : CollatzResearch.WordTrace tailWord_975511 prefixEnd_975511 74208300258998228507587 := by
  unfold tailWord_975511
  simp only [CollatzResearch.WordTrace]
  refine ⟨35579809168897725859886387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23719872779265150573257591 35579809168897725859886387)
  ·
    refine ⟨53369713753346588789829581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35579809168897725859886387 53369713753346588789829581)
    ·
      refine ⟨20013642657504970796186093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53369713753346588789829581 20013642657504970796186093)
      ·
        refine ⟨7505115996564364048569785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20013642657504970796186093 7505115996564364048569785)
        ·
          refine ⟨5628836997423273036427339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7505115996564364048569785 5628836997423273036427339)
          ·
            refine ⟨8443255496134909554641009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5628836997423273036427339 8443255496134909554641009)
            ·
              refine ⟨6332441622101182165980757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8443255496134909554641009 6332441622101182165980757)
              ·
                refine ⟨74208300258998228507587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6332441622101182165980757 74208300258998228507587)
                ·
                  rfl

theorem cell21_975511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 8].length) (baseStart_975511 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_975511 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_975511 prefixEnd_975511 := by exact prefixLift 975511
  have htrace : WordTrace (prefixWord ++ tailWord_975511) baseStart_975511 baseEnd_975511 := by
    simpa [prefixWord, tailWord_975511, baseEnd_975511] using wordTrace_append hprefix tailTrace_975511
  have hstable : (prefixWord ++ tailWord_975511).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975511).length < 2 ^ (prefixWord ++ tailWord_975511).sum := by decide
  have hdescent : baseEnd_975511 < baseStart_975511 := by decide
  rcases family_descends (prefixWord ++ tailWord_975511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975534 : List Nat := [4, 1, 4, 1, 1, 3, 1, 3, 3]
def baseStart_975534 : Nat := 118140960795 + 975534 * 2 ^ 59
def prefixEnd_975534 : Nat := 4983230072969 + 3 ^ 40 * 975534 * 2
def baseEnd_975534 : Nat := 222630149690351756639381

theorem tailTrace_975534 : CollatzResearch.WordTrace tailWord_975534 prefixEnd_975534 222630149690351756639381 := by
  unfold tailWord_975534
  simp only [CollatzResearch.WordTrace]
  refine ⟨4447581005976800098496707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23720432031876267191982437 4447581005976800098496707)
  ·
    refine ⟨6671371508965200147745061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4447581005976800098496707 6671371508965200147745061)
    ·
      refine ⟨1250882157930975027702199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6671371508965200147745061 1250882157930975027702199)
      ·
        refine ⟨1876323236896462541553299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1250882157930975027702199 1876323236896462541553299)
        ·
          refine ⟨2814484855344693812329949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1876323236896462541553299 2814484855344693812329949)
          ·
            refine ⟨1055431820754260179623731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2814484855344693812329949 1055431820754260179623731)
            ·
              refine ⟨1583147731131390269435597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1055431820754260179623731 1583147731131390269435597)
              ·
                refine ⟨593680399174271351038349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1583147731131390269435597 593680399174271351038349)
                ·
                  refine ⟨222630149690351756639381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 593680399174271351038349 222630149690351756639381)
                  ·
                    rfl

theorem cell21_975534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 3, 3].length) (baseStart_975534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_975534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_975534 prefixEnd_975534 := by exact prefixLift 975534
  have htrace : WordTrace (prefixWord ++ tailWord_975534) baseStart_975534 baseEnd_975534 := by
    simpa [prefixWord, tailWord_975534, baseEnd_975534] using wordTrace_append hprefix tailTrace_975534
  have hstable : (prefixWord ++ tailWord_975534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975534).length < 2 ^ (prefixWord ++ tailWord_975534).sum := by decide
  have hdescent : baseEnd_975534 < baseStart_975534 := by decide
  rcases family_descends (prefixWord ++ tailWord_975534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975565 : List Nat := [1, 6, 2, 1, 2, 2, 2, 1, 4]
def baseStart_975565 : Nat := 118140960795 + 975565 * 2 ^ 59
def prefixEnd_975565 : Nat := 4983230072969 + 3 ^ 40 * 975565 * 2
def baseEnd_975565 : Nat := 222637224312702591622651

theorem tailTrace_975565 : CollatzResearch.WordTrace tailWord_975565 prefixEnd_975565 222637224312702591622651 := by
  unfold tailWord_975565
  simp only [CollatzResearch.WordTrace]
  refine ⟨35581778710702093082352149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23721185807134728721568099 35581778710702093082352149)
  ·
    refine ⟨1667895877064160613235257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35581778710702093082352149 1667895877064160613235257)
    ·
      refine ⟨1250921907798120459926443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1667895877064160613235257 1250921907798120459926443)
      ·
        refine ⟨1876382861697180689889665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1250921907798120459926443 1876382861697180689889665)
        ·
          refine ⟨1407287146272885517417249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1876382861697180689889665 1407287146272885517417249)
          ·
            refine ⟨1055465359704664138062937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1407287146272885517417249 1055465359704664138062937)
            ·
              refine ⟨791599019778498103547203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1055465359704664138062937 791599019778498103547203)
              ·
                refine ⟨1187398529667747155320805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 791599019778498103547203 1187398529667747155320805)
                ·
                  refine ⟨222637224312702591622651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1187398529667747155320805 222637224312702591622651)
                  ·
                    rfl

theorem cell21_975565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_975565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_975565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_975565 prefixEnd_975565 := by exact prefixLift 975565
  have htrace : WordTrace (prefixWord ++ tailWord_975565) baseStart_975565 baseEnd_975565 := by
    simpa [prefixWord, tailWord_975565, baseEnd_975565] using wordTrace_append hprefix tailTrace_975565
  have hstable : (prefixWord ++ tailWord_975565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975565).length < 2 ^ (prefixWord ++ tailWord_975565).sum := by decide
  have hdescent : baseEnd_975565 < baseStart_975565 := by decide
  rcases family_descends (prefixWord ++ tailWord_975565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975697 : List Nat := [1, 2, 2, 1, 6, 2, 2, 5]
def baseStart_975697 : Nat := 118140960795 + 975697 * 2 ^ 59
def prefixEnd_975697 : Nat := 4983230072969 + 3 ^ 40 * 975697 * 2
def baseEnd_975697 : Nat := 74222449503699898474127

theorem tailTrace_975697 : CollatzResearch.WordTrace tailWord_975697 prefixEnd_975697 74222449503699898474127 := by
  unfold tailWord_975697
  simp only [CollatzResearch.WordTrace]
  refine ⟨35586593146223879626157345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23724395430815919750771563 35586593146223879626157345)
  ·
    refine ⟨26689944859667909719618009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35586593146223879626157345 26689944859667909719618009)
    ·
      refine ⟨20017458644750932289713507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26689944859667909719618009 20017458644750932289713507)
      ·
        refine ⟨30026187967126398434570261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20017458644750932289713507 30026187967126398434570261)
        ·
          refine ⟨1407477560959049926620481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30026187967126398434570261 1407477560959049926620481)
          ·
            refine ⟨1055608170719287444965361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1407477560959049926620481 1055608170719287444965361)
            ·
              refine ⟨791706128039465583724021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1055608170719287444965361 791706128039465583724021)
              ·
                refine ⟨74222449503699898474127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 791706128039465583724021 74222449503699898474127)
                ·
                  rfl

theorem cell21_975697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 5].length) (baseStart_975697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_975697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_975697 prefixEnd_975697 := by exact prefixLift 975697
  have htrace : WordTrace (prefixWord ++ tailWord_975697) baseStart_975697 baseEnd_975697 := by
    simpa [prefixWord, tailWord_975697, baseEnd_975697] using wordTrace_append hprefix tailTrace_975697
  have hstable : (prefixWord ++ tailWord_975697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975697).length < 2 ^ (prefixWord ++ tailWord_975697).sum := by decide
  have hdescent : baseEnd_975697 < baseStart_975697 := by decide
  rcases family_descends (prefixWord ++ tailWord_975697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975725 : List Nat := [1, 5, 1, 1, 1, 1, 1, 6, 4]
def baseStart_975725 : Nat := 118140960795 + 975725 * 2 ^ 59
def prefixEnd_975725 : Nat := 4983230072969 + 3 ^ 40 * 975725 * 2
def baseEnd_975725 : Nat := 222673738492577868955657

theorem tailTrace_975725 : CollatzResearch.WordTrace tailWord_975725 prefixEnd_975725 222673738492577868955657 := by
  unfold tailWord_975725
  simp only [CollatzResearch.WordTrace]
  refine ⟨35587614390122440408176629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23725076260081626938784419 35587614390122440408176629)
  ·
    refine ⟨3336338849073978788266559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35587614390122440408176629 3336338849073978788266559)
    ·
      refine ⟨5004508273610968182399839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3336338849073978788266559 5004508273610968182399839)
      ·
        refine ⟨7506762410416452273599759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5004508273610968182399839 7506762410416452273599759)
        ·
          refine ⟨11260143615624678410399639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7506762410416452273599759 11260143615624678410399639)
          ·
            refine ⟨16890215423437017615599459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11260143615624678410399639 16890215423437017615599459)
            ·
              refine ⟨25335323135155526423399189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16890215423437017615599459 25335323135155526423399189)
              ·
                refine ⟨1187593271960415301096837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25335323135155526423399189 1187593271960415301096837)
                ·
                  refine ⟨222673738492577868955657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1187593271960415301096837 222673738492577868955657)
                  ·
                    rfl

theorem cell21_975725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_975725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_975725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_975725 prefixEnd_975725 := by exact prefixLift 975725
  have htrace : WordTrace (prefixWord ++ tailWord_975725) baseStart_975725 baseEnd_975725 := by
    simpa [prefixWord, tailWord_975725, baseEnd_975725] using wordTrace_append hprefix tailTrace_975725
  have hstable : (prefixWord ++ tailWord_975725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975725).length < 2 ^ (prefixWord ++ tailWord_975725).sum := by decide
  have hdescent : baseEnd_975725 < baseStart_975725 := by decide
  rcases family_descends (prefixWord ++ tailWord_975725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975801 : List Nat := [1, 2, 1, 4, 2, 2, 2, 3, 4]
def baseStart_975801 : Nat := 118140960795 + 975801 * 2 ^ 59
def prefixEnd_975801 : Nat := 4983230072969 + 3 ^ 40 * 975801 * 2
def baseEnd_975801 : Nat := 222691082728018625688835

theorem tailTrace_975801 : CollatzResearch.WordTrace tailWord_975801 prefixEnd_975801 222691082728018625688835 := by
  unfold tailWord_975801
  simp only [CollatzResearch.WordTrace]
  refine ⟨35590386337847105387943257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23726924225231403591962171 35590386337847105387943257)
  ·
    refine ⟨26692789753385329040957443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35590386337847105387943257 26692789753385329040957443)
    ·
      refine ⟨40039184630077993561436165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26692789753385329040957443 40039184630077993561436165)
      ·
        refine ⟨7507347118139623792769281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40039184630077993561436165 7507347118139623792769281)
        ·
          refine ⟨5630510338604717844576961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7507347118139623792769281 5630510338604717844576961)
          ·
            refine ⟨4222882753953538383432721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5630510338604717844576961 4222882753953538383432721)
            ·
              refine ⟨3167162065465153787574541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4222882753953538383432721 3167162065465153787574541)
              ·
                refine ⟨1187685774549432670340453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3167162065465153787574541 1187685774549432670340453)
                ·
                  refine ⟨222691082728018625688835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1187685774549432670340453 222691082728018625688835)
                  ·
                    rfl

theorem cell21_975801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3, 4].length) (baseStart_975801 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_975801 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_975801 prefixEnd_975801 := by exact prefixLift 975801
  have htrace : WordTrace (prefixWord ++ tailWord_975801) baseStart_975801 baseEnd_975801 := by
    simpa [prefixWord, tailWord_975801, baseEnd_975801] using wordTrace_append hprefix tailTrace_975801
  have hstable : (prefixWord ++ tailWord_975801).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975801).length < 2 ^ (prefixWord ++ tailWord_975801).sum := by decide
  have hdescent : baseEnd_975801 < baseStart_975801 := by decide
  rcases family_descends (prefixWord ++ tailWord_975801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975880 : List Nat := [2, 1, 3, 2, 1, 5, 1, 3, 3]
def baseStart_975880 : Nat := 118140960795 + 975880 * 2 ^ 59
def prefixEnd_975880 : Nat := 4983230072969 + 3 ^ 40 * 975880 * 2
def baseEnd_975880 : Nat := 222709111604332043872007

theorem tailTrace_975880 : CollatzResearch.WordTrace tailWord_975880 prefixEnd_975880 222709111604332043872007 := by
  unfold tailWord_975880
  simp only [CollatzResearch.WordTrace]
  refine ⟨17796633852280450940034547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23728845136373934586712729 17796633852280450940034547)
  ·
    refine ⟨26694950778420676410051821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17796633852280450940034547 26694950778420676410051821)
    ·
      refine ⟨10010606541907753653769433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26694950778420676410051821 10010606541907753653769433)
      ·
        refine ⟨7507954906430815240327075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10010606541907753653769433 7507954906430815240327075)
        ·
          refine ⟨11261932359646222860490613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7507954906430815240327075 11261932359646222860490613)
          ·
            refine ⟨1055806158716833393170995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11261932359646222860490613 1055806158716833393170995)
            ·
              refine ⟨1583709238075250089756493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1055806158716833393170995 1583709238075250089756493)
              ·
                refine ⟨593890964278218783658685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1583709238075250089756493 593890964278218783658685)
                ·
                  refine ⟨222709111604332043872007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 593890964278218783658685 222709111604332043872007)
                  ·
                    rfl

theorem cell21_975880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 3, 3].length) (baseStart_975880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_975880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_975880 prefixEnd_975880 := by exact prefixLift 975880
  have htrace : WordTrace (prefixWord ++ tailWord_975880) baseStart_975880 baseEnd_975880 := by
    simpa [prefixWord, tailWord_975880, baseEnd_975880] using wordTrace_append hprefix tailTrace_975880
  have hstable : (prefixWord ++ tailWord_975880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975880).length < 2 ^ (prefixWord ++ tailWord_975880).sum := by decide
  have hdescent : baseEnd_975880 < baseStart_975880 := by decide
  rcases family_descends (prefixWord ++ tailWord_975880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975908 : List Nat := [2, 3, 1, 4, 1, 2, 2, 6]
def baseStart_975908 : Nat := 118140960795 + 975908 * 2 ^ 59
def prefixEnd_975908 : Nat := 4983230072969 + 3 ^ 40 * 975908 * 2
def baseEnd_975908 : Nat := 74238500528603405801761

theorem tailTrace_975908 : CollatzResearch.WordTrace tailWord_975908 prefixEnd_975908 74238500528603405801761 := by
  unfold tailWord_975908
  simp only [CollatzResearch.WordTrace]
  refine ⟨17797144474229731331044189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23729525965639641774725585 17797144474229731331044189)
  ·
    refine ⟨6673929177836149249141571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17797144474229731331044189 6673929177836149249141571)
    ·
      refine ⟨10010893766754223873712357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6673929177836149249141571 10010893766754223873712357)
      ·
        refine ⟨1877042581266416976321067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10010893766754223873712357 1877042581266416976321067)
        ·
          refine ⟨2815563871899625464481601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1877042581266416976321067 2815563871899625464481601)
          ·
            refine ⟨2111672903924719098361201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2815563871899625464481601 2111672903924719098361201)
            ·
              refine ⟨1583754677943539323770901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2111672903924719098361201 1583754677943539323770901)
              ·
                refine ⟨74238500528603405801761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1583754677943539323770901 74238500528603405801761)
                ·
                  rfl

theorem cell21_975908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 6].length) (baseStart_975908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_975908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_975908 prefixEnd_975908 := by exact prefixLift 975908
  have htrace : WordTrace (prefixWord ++ tailWord_975908) baseStart_975908 baseEnd_975908 := by
    simpa [prefixWord, tailWord_975908, baseEnd_975908] using wordTrace_append hprefix tailTrace_975908
  have hstable : (prefixWord ++ tailWord_975908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975908).length < 2 ^ (prefixWord ++ tailWord_975908).sum := by decide
  have hdescent : baseEnd_975908 < baseStart_975908 := by decide
  rcases family_descends (prefixWord ++ tailWord_975908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975911 : List Nat := [1, 1, 7, 1, 1, 1, 4, 1, 4]
def baseStart_975911 : Nat := 118140960795 + 975911 * 2 ^ 59
def prefixEnd_975911 : Nat := 4983230072969 + 3 ^ 40 * 975911 * 2
def baseEnd_975911 : Nat := 222716186226682878855277

theorem tailTrace_975911 : CollatzResearch.WordTrace tailWord_975911 prefixEnd_975911 222716186226682878855277 := by
  unfold tailWord_975911
  simp only [CollatzResearch.WordTrace]
  refine ⟨35594398367448594174447587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23729598911632396116298391 35594398367448594174447587)
  ·
    refine ⟨53391597551172891261671381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35594398367448594174447587 53391597551172891261671381)
    ·
      refine ⟨1251365567605614638945423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 53391597551172891261671381 1251365567605614638945423)
      ·
        refine ⟨1877048351408421958418135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1251365567605614638945423 1877048351408421958418135)
        ·
          refine ⟨2815572527112632937627203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1877048351408421958418135 2815572527112632937627203)
          ·
            refine ⟨4223358790668949406440805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2815572527112632937627203 4223358790668949406440805)
            ·
              refine ⟨791879773250428013707651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4223358790668949406440805 791879773250428013707651)
              ·
                refine ⟨1187819659875642020561477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 791879773250428013707651 1187819659875642020561477)
                ·
                  refine ⟨222716186226682878855277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1187819659875642020561477 222716186226682878855277)
                  ·
                    rfl

theorem cell21_975911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 1, 4].length) (baseStart_975911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_975911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_975911 prefixEnd_975911 := by exact prefixLift 975911
  have htrace : WordTrace (prefixWord ++ tailWord_975911) baseStart_975911 baseEnd_975911 := by
    simpa [prefixWord, tailWord_975911, baseEnd_975911] using wordTrace_append hprefix tailTrace_975911
  have hstable : (prefixWord ++ tailWord_975911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975911).length < 2 ^ (prefixWord ++ tailWord_975911).sum := by decide
  have hdescent : baseEnd_975911 < baseStart_975911 := by decide
  rcases family_descends (prefixWord ++ tailWord_975911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975956 : List Nat := [2, 4, 1, 1, 1, 1, 6, 2, 3]
def baseStart_975956 : Nat := 118140960795 + 975956 * 2 ^ 59
def prefixEnd_975956 : Nat := 4983230072969 + 3 ^ 40 * 975956 * 2
def baseEnd_975956 : Nat := 222726455839772800605185

theorem tailTrace_975956 : CollatzResearch.WordTrace tailWord_975956 prefixEnd_975956 222726455839772800605185 := by
  unfold tailWord_975956
  simp only [CollatzResearch.WordTrace]
  refine ⟨17798019826142783429917861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23730693101523711239890481 17798019826142783429917861)
  ·
    refine ⟨3337128717401771893109599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17798019826142783429917861 3337128717401771893109599)
    ·
      refine ⟨5005693076102657839664399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3337128717401771893109599 5005693076102657839664399)
      ·
        refine ⟨7508539614153986759496599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5005693076102657839664399 7508539614153986759496599)
        ·
          refine ⟨11262809421230980139244899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7508539614153986759496599 11262809421230980139244899)
          ·
            refine ⟨16894214131846470208867349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11262809421230980139244899 16894214131846470208867349)
            ·
              refine ⟨791916287430303291040657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16894214131846470208867349 791916287430303291040657)
              ·
                refine ⟨593937215572727468280493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 791916287430303291040657 593937215572727468280493)
                ·
                  refine ⟨222726455839772800605185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 593937215572727468280493 222726455839772800605185)
                  ·
                    rfl

theorem cell21_975956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_975956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_975956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_975956 prefixEnd_975956 := by exact prefixLift 975956
  have htrace : WordTrace (prefixWord ++ tailWord_975956) baseStart_975956 baseEnd_975956 := by
    simpa [prefixWord, tailWord_975956, baseEnd_975956] using wordTrace_append hprefix tailTrace_975956
  have hstable : (prefixWord ++ tailWord_975956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975956).length < 2 ^ (prefixWord ++ tailWord_975956).sum := by decide
  have hdescent : baseEnd_975956 < baseStart_975956 := by decide
  rcases family_descends (prefixWord ++ tailWord_975956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975970 : List Nat := [3, 3, 2, 2, 1, 1, 2, 3, 4]
def baseStart_975970 : Nat := 118140960795 + 975970 * 2 ^ 59
def prefixEnd_975970 : Nat := 4983230072969 + 3 ^ 40 * 975970 * 2
def baseEnd_975970 : Nat := 222729650830511887371823

theorem tailTrace_975970 : CollatzResearch.WordTrace tailWord_975970 prefixEnd_975970 222729650830511887371823 := by
  unfold tailWord_975970
  simp only [CollatzResearch.WordTrace]
  refine ⟨8899137568558711812711341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23731033516156564833896909 8899137568558711812711341)
  ·
    refine ⟨3337176588209516929766753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8899137568558711812711341 3337176588209516929766753)
    ·
      refine ⟨2502882441157137697325065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3337176588209516929766753 2502882441157137697325065)
      ·
        refine ⟨1877161830867853272993799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2502882441157137697325065 1877161830867853272993799)
        ·
          refine ⟨2815742746301779909490699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1877161830867853272993799 2815742746301779909490699)
          ·
            refine ⟨4223614119452669864236049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2815742746301779909490699 4223614119452669864236049)
            ·
              refine ⟨3167710589589502398177037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4223614119452669864236049 3167710589589502398177037)
              ·
                refine ⟨1187891471096063399316389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3167710589589502398177037 1187891471096063399316389)
                ·
                  refine ⟨222729650830511887371823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1187891471096063399316389 222729650830511887371823)
                  ·
                    rfl

theorem cell21_975970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_975970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_975970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_975970 prefixEnd_975970 := by exact prefixLift 975970
  have htrace : WordTrace (prefixWord ++ tailWord_975970) baseStart_975970 baseEnd_975970 := by
    simpa [prefixWord, tailWord_975970, baseEnd_975970] using wordTrace_append hprefix tailTrace_975970
  have hstable : (prefixWord ++ tailWord_975970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975970).length < 2 ^ (prefixWord ++ tailWord_975970).sum := by decide
  have hdescent : baseEnd_975970 < baseStart_975970 := by decide
  rcases family_descends (prefixWord ++ tailWord_975970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976066 : List Nat := [3, 5, 1, 1, 3, 1, 1, 1, 5]
def baseStart_976066 : Nat := 118140960795 + 976066 * 2 ^ 59
def prefixEnd_976066 : Nat := 4983230072969 + 3 ^ 40 * 976066 * 2
def baseEnd_976066 : Nat := 222751559338437053771627

theorem tailTrace_976066 : CollatzResearch.WordTrace tailWord_976066 prefixEnd_976066 222751559338437053771627 := by
  unfold tailWord_976066
  simp only [CollatzResearch.WordTrace]
  refine ⟨8900012920471763911585013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23733367787924703764226701 8900012920471763911585013)
  ·
    refine ⟨834376211294227866711095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8900012920471763911585013 834376211294227866711095)
    ·
      refine ⟨1251564316941341800066643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 834376211294227866711095 1251564316941341800066643)
      ·
        refine ⟨1877346475412012700099965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1251564316941341800066643 1877346475412012700099965)
        ·
          refine ⟨704004928279504762537487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1877346475412012700099965 704004928279504762537487)
          ·
            refine ⟨1056007392419257143806231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704004928279504762537487 1056007392419257143806231)
            ·
              refine ⟨1584011088628885715709347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1056007392419257143806231 1584011088628885715709347)
              ·
                refine ⟨2376016632943328573564021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1584011088628885715709347 2376016632943328573564021)
                ·
                  refine ⟨222751559338437053771627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2376016632943328573564021 222751559338437053771627)
                  ·
                    rfl

theorem cell21_976066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_976066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_976066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_976066 prefixEnd_976066 := by exact prefixLift 976066
  have htrace : WordTrace (prefixWord ++ tailWord_976066) baseStart_976066 baseEnd_976066 := by
    simpa [prefixWord, tailWord_976066, baseEnd_976066] using wordTrace_append hprefix tailTrace_976066
  have hstable : (prefixWord ++ tailWord_976066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976066).length < 2 ^ (prefixWord ++ tailWord_976066).sum := by decide
  have hdescent : baseEnd_976066 < baseStart_976066 := by decide
  rcases family_descends (prefixWord ++ tailWord_976066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976074 : List Nat := [3, 1, 2, 1, 3, 2, 3, 1, 5]
def baseStart_976074 : Nat := 118140960795 + 976074 * 2 ^ 59
def prefixEnd_976074 : Nat := 4983230072969 + 3 ^ 40 * 976074 * 2
def baseEnd_976074 : Nat := 222753385047430817638277

theorem tailTrace_976074 : CollatzResearch.WordTrace tailWord_976074 prefixEnd_976074 222753385047430817638277 := by
  unfold tailWord_976074
  simp only [CollatzResearch.WordTrace]
  refine ⟨8900085866464518253157819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23733562310572048675087517 8900085866464518253157819)
  ·
    refine ⟨13350128799696777379736729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8900085866464518253157819 13350128799696777379736729)
    ·
      refine ⟨10012596599772583034802547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13350128799696777379736729 10012596599772583034802547)
      ·
        refine ⟨15018894899658874552203821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10012596599772583034802547 15018894899658874552203821)
        ·
          refine ⟨5632085587372077957076433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15018894899658874552203821 5632085587372077957076433)
          ·
            refine ⟨4224064190529058467807325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5632085587372077957076433 4224064190529058467807325)
            ·
              refine ⟨1584024071448396925427747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4224064190529058467807325 1584024071448396925427747)
              ·
                refine ⟨2376036107172595388141621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1584024071448396925427747 2376036107172595388141621)
                ·
                  refine ⟨222753385047430817638277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2376036107172595388141621 222753385047430817638277)
                  ·
                    rfl

theorem cell21_976074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 5].length) (baseStart_976074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_976074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_976074 prefixEnd_976074 := by exact prefixLift 976074
  have htrace : WordTrace (prefixWord ++ tailWord_976074) baseStart_976074 baseEnd_976074 := by
    simpa [prefixWord, tailWord_976074, baseEnd_976074] using wordTrace_append hprefix tailTrace_976074
  have hstable : (prefixWord ++ tailWord_976074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976074).length < 2 ^ (prefixWord ++ tailWord_976074).sum := by decide
  have hdescent : baseEnd_976074 < baseStart_976074 := by decide
  rcases family_descends (prefixWord ++ tailWord_976074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976133 : List Nat := [1, 3, 1, 1, 2, 1, 4, 3, 5]
def baseStart_976133 : Nat := 118140960795 + 976133 * 2 ^ 59
def prefixEnd_976133 : Nat := 4983230072969 + 3 ^ 40 * 976133 * 2
def baseEnd_976133 : Nat := 222766849651259826154823

theorem tailTrace_976133 : CollatzResearch.WordTrace tailWord_976133 prefixEnd_976133 222766849651259826154823 := by
  unfold tailWord_976133
  simp only [CollatzResearch.WordTrace]
  refine ⟨35602495372644326089029053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23734996915096217392686035 35602495372644326089029053)
  ·
    refine ⟨13350935764741622283385895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35602495372644326089029053 13350935764741622283385895)
    ·
      refine ⟨20026403647112433425078843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13350935764741622283385895 20026403647112433425078843)
      ·
        refine ⟨30039605470668650137618265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20026403647112433425078843 30039605470668650137618265)
        ·
          refine ⟨22529704103001487603213699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30039605470668650137618265 22529704103001487603213699)
          ·
            refine ⟨33794556154502231404820549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22529704103001487603213699 33794556154502231404820549)
            ·
              refine ⟨6336479278969168388403853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33794556154502231404820549 6336479278969168388403853)
              ·
                refine ⟨2376179729613438145651445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6336479278969168388403853 2376179729613438145651445)
                ·
                  refine ⟨222766849651259826154823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2376179729613438145651445 222766849651259826154823)
                  ·
                    rfl

theorem cell21_976133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_976133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_976133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_976133 prefixEnd_976133 := by exact prefixLift 976133
  have htrace : WordTrace (prefixWord ++ tailWord_976133) baseStart_976133 baseEnd_976133 := by
    simpa [prefixWord, tailWord_976133, baseEnd_976133] using wordTrace_append hprefix tailTrace_976133
  have hstable : (prefixWord ++ tailWord_976133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976133).length < 2 ^ (prefixWord ++ tailWord_976133).sum := by decide
  have hdescent : baseEnd_976133 < baseStart_976133 := by decide
  rcases family_descends (prefixWord ++ tailWord_976133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976136 : List Nat := [2, 1, 3, 2, 4, 2, 1, 6]
def baseStart_976136 : Nat := 118140960795 + 976136 * 2 ^ 59
def prefixEnd_976136 : Nat := 4983230072969 + 3 ^ 40 * 976136 * 2
def baseEnd_976136 : Nat := 74255844764044162534939

theorem tailTrace_976136 : CollatzResearch.WordTrace tailWord_976136 prefixEnd_976136 74255844764044162534939 := by
  unfold tailWord_976136
  simp only [CollatzResearch.WordTrace]
  refine ⟨17801302395816728800694131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23735069861088971734258841 17801302395816728800694131)
  ·
    refine ⟨26701953593725093201041197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17801302395816728800694131 26701953593725093201041197)
    ·
      refine ⟨10013232597646909950390449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26701953593725093201041197 10013232597646909950390449)
      ·
        refine ⟨7509924448235182462792837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10013232597646909950390449 7509924448235182462792837)
        ·
          refine ⟨1408110834044096711773657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7509924448235182462792837 1408110834044096711773657)
          ·
            refine ⟨1056083125533072533830243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1408110834044096711773657 1056083125533072533830243)
            ·
              refine ⟨1584124688299608800745365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1056083125533072533830243 1584124688299608800745365)
              ·
                refine ⟨74255844764044162534939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1584124688299608800745365 74255844764044162534939)
                ·
                  rfl

theorem cell21_976136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 6].length) (baseStart_976136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_976136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_976136 prefixEnd_976136 := by exact prefixLift 976136
  have htrace : WordTrace (prefixWord ++ tailWord_976136) baseStart_976136 baseEnd_976136 := by
    simpa [prefixWord, tailWord_976136, baseEnd_976136] using wordTrace_append hprefix tailTrace_976136
  have hstable : (prefixWord ++ tailWord_976136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976136).length < 2 ^ (prefixWord ++ tailWord_976136).sum := by decide
  have hdescent : baseEnd_976136 < baseStart_976136 := by decide
  rcases family_descends (prefixWord ++ tailWord_976136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976147 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 10]
def baseStart_976147 : Nat := 118140960795 + 976147 * 2 ^ 59
def prefixEnd_976147 : Nat := 4983230072969 + 3 ^ 40 * 976147 * 2
def baseEnd_976147 : Nat := 222770044641998912921461

theorem tailTrace_976147 : CollatzResearch.WordTrace tailWord_976147 prefixEnd_976147 222770044641998912921461 := by
  unfold tailWord_976147
  simp only [CollatzResearch.WordTrace]
  refine ⟨35603005994593606480038695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23735337329729070986692463 35603005994593606480038695)
  ·
    refine ⟨53404508991890409720058043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35603005994593606480038695 53404508991890409720058043)
    ·
      refine ⟨80106763487835614580087065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53404508991890409720058043 80106763487835614580087065)
      ·
        refine ⟨60080072615876710935065299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80106763487835614580087065 60080072615876710935065299)
        ·
          refine ⟨90120108923815066402597949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60080072615876710935065299 90120108923815066402597949)
          ·
            refine ⟨33795040846430649900974231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90120108923815066402597949 33795040846430649900974231)
            ·
              refine ⟨50692561269645974851461347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33795040846430649900974231 50692561269645974851461347)
              ·
                refine ⟨76038841904468962277192021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50692561269645974851461347 76038841904468962277192021)
                ·
                  refine ⟨222770044641998912921461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 76038841904468962277192021 222770044641998912921461)
                  ·
                    rfl

theorem cell21_976147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 10].length) (baseStart_976147 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_976147 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_976147 prefixEnd_976147 := by exact prefixLift 976147
  have htrace : WordTrace (prefixWord ++ tailWord_976147) baseStart_976147 baseEnd_976147 := by
    simpa [prefixWord, tailWord_976147, baseEnd_976147] using wordTrace_append hprefix tailTrace_976147
  have hstable : (prefixWord ++ tailWord_976147).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976147).length < 2 ^ (prefixWord ++ tailWord_976147).sum := by decide
  have hdescent : baseEnd_976147 < baseStart_976147 := by decide
  rcases family_descends (prefixWord ++ tailWord_976147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976164 : List Nat := [2, 3, 1, 3, 1, 1, 2, 2, 6]
def baseStart_976164 : Nat := 118140960795 + 976164 * 2 ^ 59
def prefixEnd_976164 : Nat := 4983230072969 + 3 ^ 40 * 976164 * 2
def baseEnd_976164 : Nat := 222773924273610661138093

theorem tailTrace_976164 : CollatzResearch.WordTrace tailWord_976164 prefixEnd_976164 222773924273610661138093 := by
  unfold tailWord_976164
  simp only [CollatzResearch.WordTrace]
  refine ⟨17801813017766009191703773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23735750690354678922271697 17801813017766009191703773)
  ·
    refine ⟨6675679881662253446888915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17801813017766009191703773 6675679881662253446888915)
    ·
      refine ⟨10013519822493380170333373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6675679881662253446888915 10013519822493380170333373)
      ·
        refine ⟨3755069933435017563875015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10013519822493380170333373 3755069933435017563875015)
        ·
          refine ⟨5632604900152526345812523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3755069933435017563875015 5632604900152526345812523)
          ·
            refine ⟨8448907350228789518718785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5632604900152526345812523 8448907350228789518718785)
            ·
              refine ⟨6336680512671592139039089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8448907350228789518718785 6336680512671592139039089)
              ·
                refine ⟨4752510384503694104279317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6336680512671592139039089 4752510384503694104279317)
                ·
                  refine ⟨222773924273610661138093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4752510384503694104279317 222773924273610661138093)
                  ·
                    rfl

theorem cell21_976164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_976164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_976164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_976164 prefixEnd_976164 := by exact prefixLift 976164
  have htrace : WordTrace (prefixWord ++ tailWord_976164) baseStart_976164 baseEnd_976164 := by
    simpa [prefixWord, tailWord_976164, baseEnd_976164] using wordTrace_append hprefix tailTrace_976164
  have hstable : (prefixWord ++ tailWord_976164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976164).length < 2 ^ (prefixWord ++ tailWord_976164).sum := by decide
  have hdescent : baseEnd_976164 < baseStart_976164 := by decide
  rcases family_descends (prefixWord ++ tailWord_976164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976181 : List Nat := [1, 3, 3, 1, 2, 2, 3, 2, 4]
def baseStart_976181 : Nat := 118140960795 + 976181 * 2 ^ 59
def prefixEnd_976181 : Nat := 4983230072969 + 3 ^ 40 * 976181 * 2
def baseEnd_976181 : Nat := 222777803905222409354725

theorem tailTrace_976181 : CollatzResearch.WordTrace tailWord_976181 prefixEnd_976181 222777803905222409354725 := by
  unfold tailWord_976181
  simp only [CollatzResearch.WordTrace]
  refine ⟨35604246076470430286776397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23736164050980286857850931 35604246076470430286776397)
  ·
    refine ⟨13351592278676411357541149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35604246076470430286776397 13351592278676411357541149)
    ·
      refine ⟨5006847104503654259077931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13351592278676411357541149 5006847104503654259077931)
      ·
        refine ⟨7510270656755481388616897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5006847104503654259077931 7510270656755481388616897)
        ·
          refine ⟨5632702992566611041462673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7510270656755481388616897 5632702992566611041462673)
          ·
            refine ⟨4224527244424958281097005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5632702992566611041462673 4224527244424958281097005)
            ·
              refine ⟨1584197716659359355411377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4224527244424958281097005 1584197716659359355411377)
              ·
                refine ⟨1188148287494519516558533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1584197716659359355411377 1188148287494519516558533)
                ·
                  refine ⟨222777803905222409354725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1188148287494519516558533 222777803905222409354725)
                  ·
                    rfl

theorem cell21_976181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2, 4].length) (baseStart_976181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_976181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_976181 prefixEnd_976181 := by exact prefixLift 976181
  have htrace : WordTrace (prefixWord ++ tailWord_976181) baseStart_976181 baseEnd_976181 := by
    simpa [prefixWord, tailWord_976181, baseEnd_976181] using wordTrace_append hprefix tailTrace_976181
  have hstable : (prefixWord ++ tailWord_976181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976181).length < 2 ^ (prefixWord ++ tailWord_976181).sum := by decide
  have hdescent : baseEnd_976181 < baseStart_976181 := by decide
  rcases family_descends (prefixWord ++ tailWord_976181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976209 : List Nat := [1, 2, 2, 1, 4, 1, 1, 4, 5]
def baseStart_976209 : Nat := 118140960795 + 976209 * 2 ^ 59
def prefixEnd_976209 : Nat := 4983230072969 + 3 ^ 40 * 976209 * 2
def baseEnd_976209 : Nat := 222784193886700582888001

theorem tailTrace_976209 : CollatzResearch.WordTrace tailWord_976209 prefixEnd_976209 222784193886700582888001 := by
  unfold tailWord_976209
  simp only [CollatzResearch.WordTrace]
  refine ⟨35605267320368991068795681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23736844880245994045863787 35605267320368991068795681)
  ·
    refine ⟨26703950490276743301596761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35605267320368991068795681 26703950490276743301596761)
    ·
      refine ⟨20027962867707557476197571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26703950490276743301596761 20027962867707557476197571)
      ·
        refine ⟨30041944301561336214296357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20027962867707557476197571 30041944301561336214296357)
        ·
          refine ⟨5632864556542750540180567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30041944301561336214296357 5632864556542750540180567)
          ·
            refine ⟨8449296834814125810270851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5632864556542750540180567 8449296834814125810270851)
            ·
              refine ⟨12673945252221188715406277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8449296834814125810270851 12673945252221188715406277)
              ·
                refine ⟨2376364734791472884138677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12673945252221188715406277 2376364734791472884138677)
                ·
                  refine ⟨222784193886700582888001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2376364734791472884138677 222784193886700582888001)
                  ·
                    rfl

theorem cell21_976209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 5].length) (baseStart_976209 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_976209 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_976209 prefixEnd_976209 := by exact prefixLift 976209
  have htrace : WordTrace (prefixWord ++ tailWord_976209) baseStart_976209 baseEnd_976209 := by
    simpa [prefixWord, tailWord_976209, baseEnd_976209] using wordTrace_append hprefix tailTrace_976209
  have hstable : (prefixWord ++ tailWord_976209).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976209).length < 2 ^ (prefixWord ++ tailWord_976209).sum := by decide
  have hdescent : baseEnd_976209 < baseStart_976209 := by decide
  rcases family_descends (prefixWord ++ tailWord_976209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976240 : List Nat := [2, 1, 1, 1, 4, 2, 2, 4, 4]
def baseStart_976240 : Nat := 118140960795 + 976240 * 2 ^ 59
def prefixEnd_976240 : Nat := 4983230072969 + 3 ^ 40 * 976240 * 2
def baseEnd_976240 : Nat := 222791268509051417871271

theorem tailTrace_976240 : CollatzResearch.WordTrace tailWord_976240 prefixEnd_976240 222791268509051417871271 := by
  unfold tailWord_976240
  simp only [CollatzResearch.WordTrace]
  refine ⟨17803198991628341681587087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23737598655504455575449449 17803198991628341681587087)
  ·
    refine ⟨26704798487442512522380631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17803198991628341681587087 26704798487442512522380631)
    ·
      refine ⟨40057197731163768783570947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26704798487442512522380631 40057197731163768783570947)
      ·
        refine ⟨60085796596745653175356421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40057197731163768783570947 60085796596745653175356421)
        ·
          refine ⟨11266086861889809970379329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60085796596745653175356421 11266086861889809970379329)
          ·
            refine ⟨8449565146417357477784497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11266086861889809970379329 8449565146417357477784497)
            ·
              refine ⟨6337173859813018108338373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8449565146417357477784497 6337173859813018108338373)
              ·
                refine ⟨1188220098714940895313445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6337173859813018108338373 1188220098714940895313445)
                ·
                  refine ⟨222791268509051417871271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1188220098714940895313445 222791268509051417871271)
                  ·
                    rfl

theorem cell21_976240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4, 4].length) (baseStart_976240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_976240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_976240 prefixEnd_976240 := by exact prefixLift 976240
  have htrace : WordTrace (prefixWord ++ tailWord_976240) baseStart_976240 baseEnd_976240 := by
    simpa [prefixWord, tailWord_976240, baseEnd_976240] using wordTrace_append hprefix tailTrace_976240
  have hstable : (prefixWord ++ tailWord_976240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976240).length < 2 ^ (prefixWord ++ tailWord_976240).sum := by decide
  have hdescent : baseEnd_976240 < baseStart_976240 := by decide
  rcases family_descends (prefixWord ++ tailWord_976240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976471 : List Nat := [1, 1, 3, 2, 2, 3, 4, 2, 3]
def baseStart_976471 : Nat := 118140960795 + 976471 * 2 ^ 59
def prefixEnd_976471 : Nat := 4983230072969 + 3 ^ 40 * 976471 * 2
def baseEnd_976471 : Nat := 222843985856246349520799

theorem tailTrace_976471 : CollatzResearch.WordTrace tailWord_976471 prefixEnd_976471 222843985856246349520799 := by
  unfold tailWord_976471
  simp only [CollatzResearch.WordTrace]
  refine ⟨35614823245419809814833267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23743215496946539876555511 35614823245419809814833267)
  ·
    refine ⟨53422234868129714722249901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35614823245419809814833267 53422234868129714722249901)
    ·
      refine ⟨20033338075548643020843713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53422234868129714722249901 20033338075548643020843713)
      ·
        refine ⟨15025003556661482265632785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20033338075548643020843713 15025003556661482265632785)
        ·
          refine ⟨11268752667496111699224589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15025003556661482265632785 11268752667496111699224589)
          ·
            refine ⟨4225782250311041887209221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11268752667496111699224589 4225782250311041887209221)
            ·
              refine ⟨792334171933320353851729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4225782250311041887209221 792334171933320353851729)
              ·
                refine ⟨594250628949990265388797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 792334171933320353851729 594250628949990265388797)
                ·
                  refine ⟨222843985856246349520799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 594250628949990265388797 222843985856246349520799)
                  ·
                    rfl

theorem cell21_976471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 2, 3].length) (baseStart_976471 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_976471 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_976471 prefixEnd_976471 := by exact prefixLift 976471
  have htrace : WordTrace (prefixWord ++ tailWord_976471) baseStart_976471 baseEnd_976471 := by
    simpa [prefixWord, tailWord_976471, baseEnd_976471] using wordTrace_append hprefix tailTrace_976471
  have hstable : (prefixWord ++ tailWord_976471).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976471).length < 2 ^ (prefixWord ++ tailWord_976471).sum := by decide
  have hdescent : baseEnd_976471 < baseStart_976471 := by decide
  rcases family_descends (prefixWord ++ tailWord_976471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976696 : List Nat := [2, 1, 2, 1, 3, 3, 3, 2, 4]
def baseStart_976696 : Nat := 118140960795 + 976696 * 2 ^ 59
def prefixEnd_976696 : Nat := 4983230072969 + 3 ^ 40 * 976696 * 2
def baseEnd_976696 : Nat := 222895333921695958270339

theorem tailTrace_976696 : CollatzResearch.WordTrace tailWord_976696 prefixEnd_976696 222895333921695958270339 := by
  unfold tailWord_976696
  simp only [CollatzResearch.WordTrace]
  refine ⟨17811514834802336620886971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23748686446403115494515961 17811514834802336620886971)
  ·
    refine ⟨26717272252203504931330457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17811514834802336620886971 26717272252203504931330457)
    ·
      refine ⟨20037954189152628698497843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26717272252203504931330457 20037954189152628698497843)
      ·
        refine ⟨30056931283728943047746765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20037954189152628698497843 30056931283728943047746765)
        ·
          refine ⟨11271349231398353642905037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30056931283728943047746765 11271349231398353642905037)
          ·
            refine ⟨4226755961774382616089389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11271349231398353642905037 4226755961774382616089389)
            ·
              refine ⟨1585033485665393481033521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4226755961774382616089389 1585033485665393481033521)
              ·
                refine ⟨1188775114249045110775141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1585033485665393481033521 1188775114249045110775141)
                ·
                  refine ⟨222895333921695958270339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1188775114249045110775141 222895333921695958270339)
                  ·
                    rfl

theorem cell21_976696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2, 4].length) (baseStart_976696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_976696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_976696 prefixEnd_976696 := by exact prefixLift 976696
  have htrace : WordTrace (prefixWord ++ tailWord_976696) baseStart_976696 baseEnd_976696 := by
    simpa [prefixWord, tailWord_976696, baseEnd_976696] using wordTrace_append hprefix tailTrace_976696
  have hstable : (prefixWord ++ tailWord_976696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976696).length < 2 ^ (prefixWord ++ tailWord_976696).sum := by decide
  have hdescent : baseEnd_976696 < baseStart_976696 := by decide
  rcases family_descends (prefixWord ++ tailWord_976696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976755 : List Nat := [1, 1, 1, 2, 2, 1, 3, 6, 4]
def baseStart_976755 : Nat := 118140960795 + 976755 * 2 ^ 59
def prefixEnd_976755 : Nat := 4983230072969 + 3 ^ 40 * 976755 * 2
def baseEnd_976755 : Nat := 222908798525524966786885

theorem tailTrace_976755 : CollatzResearch.WordTrace tailWord_976755 prefixEnd_976755 222908798525524966786885 := by
  unfold tailWord_976755
  simp only [CollatzResearch.WordTrace]
  refine ⟨35625181576390926318171719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23750121050927284212114479 35625181576390926318171719)
  ·
    refine ⟨53437772364586389477257579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35625181576390926318171719 53437772364586389477257579)
    ·
      refine ⟨80156658546879584215886369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53437772364586389477257579 80156658546879584215886369)
      ·
        refine ⟨60117493910159688161914777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80156658546879584215886369 60117493910159688161914777)
        ·
          refine ⟨45088120432619766121436083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60117493910159688161914777 45088120432619766121436083)
          ·
            refine ⟨67632180648929649182154125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45088120432619766121436083 67632180648929649182154125)
            ·
              refine ⟨25362067743348618443307797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67632180648929649182154125 25362067743348618443307797)
              ·
                refine ⟨1188846925469466489530053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25362067743348618443307797 1188846925469466489530053)
                ·
                  refine ⟨222908798525524966786885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1188846925469466489530053 222908798525524966786885)
                  ·
                    rfl

theorem cell21_976755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6, 4].length) (baseStart_976755 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_976755 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_976755 prefixEnd_976755 := by exact prefixLift 976755
  have htrace : WordTrace (prefixWord ++ tailWord_976755) baseStart_976755 baseEnd_976755 := by
    simpa [prefixWord, tailWord_976755, baseEnd_976755] using wordTrace_append hprefix tailTrace_976755
  have hstable : (prefixWord ++ tailWord_976755).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976755).length < 2 ^ (prefixWord ++ tailWord_976755).sum := by decide
  have hdescent : baseEnd_976755 < baseStart_976755 := by decide
  rcases family_descends (prefixWord ++ tailWord_976755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976831 : List Nat := [1, 1, 2, 2, 2, 1, 3, 5, 4]
def baseStart_976831 : Nat := 118140960795 + 976831 * 2 ^ 59
def prefixEnd_976831 : Nat := 4983230072969 + 3 ^ 40 * 976831 * 2
def baseEnd_976831 : Nat := 222926142760965723520063

theorem tailTrace_976831 : CollatzResearch.WordTrace tailWord_976831 prefixEnd_976831 222926142760965723520063 := by
  unfold tailWord_976831
  simp only [CollatzResearch.WordTrace]
  refine ⟨35627953524115591297938347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23751969016077060865292231 35627953524115591297938347)
  ·
    refine ⟨53441930286173386946907521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35627953524115591297938347 53441930286173386946907521)
    ·
      refine ⟨40081447714630040210180641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53441930286173386946907521 40081447714630040210180641)
      ·
        refine ⟨30061085785972530157635481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40081447714630040210180641 30061085785972530157635481)
        ·
          refine ⟨22545814339479397618226611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30061085785972530157635481 22545814339479397618226611)
          ·
            refine ⟨33818721509219096427339917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22545814339479397618226611 33818721509219096427339917)
            ·
              refine ⟨12682020565957161160252469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33818721509219096427339917 12682020565957161160252469)
              ·
                refine ⟨1188939428058483858773669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12682020565957161160252469 1188939428058483858773669)
                ·
                  refine ⟨222926142760965723520063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1188939428058483858773669 222926142760965723520063)
                  ·
                    rfl

theorem cell21_976831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5, 4].length) (baseStart_976831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_976831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_976831 prefixEnd_976831 := by exact prefixLift 976831
  have htrace : WordTrace (prefixWord ++ tailWord_976831) baseStart_976831 baseEnd_976831 := by
    simpa [prefixWord, tailWord_976831, baseEnd_976831] using wordTrace_append hprefix tailTrace_976831
  have hstable : (prefixWord ++ tailWord_976831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976831).length < 2 ^ (prefixWord ++ tailWord_976831).sum := by decide
  have hdescent : baseEnd_976831 < baseStart_976831 := by decide
  rcases family_descends (prefixWord ++ tailWord_976831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976938 : List Nat := [3, 1, 4, 1, 2, 1, 1, 8]
def baseStart_976938 : Nat := 118140960795 + 976938 * 2 ^ 59
def prefixEnd_976938 : Nat := 4983230072969 + 3 ^ 40 * 976938 * 2
def baseEnd_976938 : Nat := 74316853872919105078837

theorem tailTrace_976938 : CollatzResearch.WordTrace tailWord_976938 prefixEnd_976938 74316853872919105078837 := by
  unfold tailWord_976938
  simp only [CollatzResearch.WordTrace]
  refine ⟨8907964033681987143020867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23754570756485299048055645 8907964033681987143020867)
  ·
    refine ⟨13361946050522980714531301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8907964033681987143020867 13361946050522980714531301)
    ·
      refine ⟨2505364884473058883974619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13361946050522980714531301 2505364884473058883974619)
      ·
        refine ⟨3758047326709588325961929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2505364884473058883974619 3758047326709588325961929)
        ·
          refine ⟨2818535495032191244471447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3758047326709588325961929 2818535495032191244471447)
          ·
            refine ⟨4227803242548286866707171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2818535495032191244471447 4227803242548286866707171)
            ·
              refine ⟨6341704863822430300060757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4227803242548286866707171 6341704863822430300060757)
              ·
                refine ⟨74316853872919105078837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6341704863822430300060757 74316853872919105078837)
                ·
                  rfl

theorem cell21_976938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 8].length) (baseStart_976938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_976938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_976938 prefixEnd_976938 := by exact prefixLift 976938
  have htrace : WordTrace (prefixWord ++ tailWord_976938) baseStart_976938 baseEnd_976938 := by
    simpa [prefixWord, tailWord_976938, baseEnd_976938] using wordTrace_append hprefix tailTrace_976938
  have hstable : (prefixWord ++ tailWord_976938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976938).length < 2 ^ (prefixWord ++ tailWord_976938).sum := by decide
  have hdescent : baseEnd_976938 < baseStart_976938 := by decide
  rcases family_descends (prefixWord ++ tailWord_976938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976969 : List Nat := [1, 2, 1, 1, 2, 2, 4, 5, 3]
def baseStart_976969 : Nat := 118140960795 + 976969 * 2 ^ 59
def prefixEnd_976969 : Nat := 4983230072969 + 3 ^ 40 * 976969 * 2
def baseEnd_976969 : Nat := 222957636241108150219781

theorem tailTrace_976969 : CollatzResearch.WordTrace tailWord_976969 prefixEnd_976969 222957636241108150219781 := by
  unfold tailWord_976969
  simp only [CollatzResearch.WordTrace]
  refine ⟨35632986797615640866461961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23755324531743760577641307 35632986797615640866461961)
  ·
    refine ⟨26724740098211730649846471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35632986797615640866461961 26724740098211730649846471)
    ·
      refine ⟨40087110147317595974769707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26724740098211730649846471 40087110147317595974769707)
      ·
        refine ⟨60130665220976393962154561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40087110147317595974769707 60130665220976393962154561)
        ·
          refine ⟨45097998915732295471615921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60130665220976393962154561 45097998915732295471615921)
          ·
            refine ⟨33823499186799221603711941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45097998915732295471615921 33823499186799221603711941)
            ·
              refine ⟨6341906097524854050695989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33823499186799221603711941 6341906097524854050695989)
              ·
                refine ⟨594553696642955067252749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6341906097524854050695989 594553696642955067252749)
                ·
                  refine ⟨222957636241108150219781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 594553696642955067252749 222957636241108150219781)
                  ·
                    rfl

theorem cell21_976969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 5, 3].length) (baseStart_976969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_976969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_976969 prefixEnd_976969 := by exact prefixLift 976969
  have htrace : WordTrace (prefixWord ++ tailWord_976969) baseStart_976969 baseEnd_976969 := by
    simpa [prefixWord, tailWord_976969, baseEnd_976969] using wordTrace_append hprefix tailTrace_976969
  have hstable : (prefixWord ++ tailWord_976969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976969).length < 2 ^ (prefixWord ++ tailWord_976969).sum := by decide
  have hdescent : baseEnd_976969 < baseStart_976969 := by decide
  rcases family_descends (prefixWord ++ tailWord_976969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976983 : List Nat := [1, 1, 3, 2, 2, 1, 3, 4, 4]
def baseStart_976983 : Nat := 118140960795 + 976983 * 2 ^ 59
def prefixEnd_976983 : Nat := 4983230072969 + 3 ^ 40 * 976983 * 2
def baseEnd_976983 : Nat := 222960831231847236986419

theorem tailTrace_976983 : CollatzResearch.WordTrace tailWord_976983 prefixEnd_976983 222960831231847236986419 := by
  unfold tailWord_976983
  simp only [CollatzResearch.WordTrace]
  refine ⟨35633497419564921257471603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23755664946376614171647735 35633497419564921257471603)
  ·
    refine ⟨53450246129347381886207405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35633497419564921257471603 53450246129347381886207405)
    ·
      refine ⟨20043842298505268207327777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53450246129347381886207405 20043842298505268207327777)
      ·
        refine ⟨15032881723878951155495833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20043842298505268207327777 15032881723878951155495833)
        ·
          refine ⟨11274661292909213366621875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15032881723878951155495833 11274661292909213366621875)
          ·
            refine ⟨16911991939363820049932813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11274661292909213366621875 16911991939363820049932813)
            ·
              refine ⟨6341996977261432518724805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16911991939363820049932813 6341996977261432518724805)
              ·
                refine ⟨1189124433236518597260901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6341996977261432518724805 1189124433236518597260901)
                ·
                  refine ⟨222960831231847236986419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1189124433236518597260901 222960831231847236986419)
                  ·
                    rfl

theorem cell21_976983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4, 4].length) (baseStart_976983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_976983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_976983 prefixEnd_976983 := by exact prefixLift 976983
  have htrace : WordTrace (prefixWord ++ tailWord_976983) baseStart_976983 baseEnd_976983 := by
    simpa [prefixWord, tailWord_976983, baseEnd_976983] using wordTrace_append hprefix tailTrace_976983
  have hstable : (prefixWord ++ tailWord_976983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976983).length < 2 ^ (prefixWord ++ tailWord_976983).sum := by decide
  have hdescent : baseEnd_976983 < baseStart_976983 := by decide
  rcases family_descends (prefixWord ++ tailWord_976983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977028 : List Nat := [2, 3, 2, 1, 2, 1, 1, 2, 7]
def baseStart_977028 : Nat := 118140960795 + 977028 * 2 ^ 59
def prefixEnd_977028 : Nat := 4983230072969 + 3 ^ 40 * 977028 * 2
def baseEnd_977028 : Nat := 222971100844937158736327

theorem tailTrace_977028 : CollatzResearch.WordTrace tailWord_977028 prefixEnd_977028 222971100844937158736327 := by
  unfold tailWord_977028
  simp only [CollatzResearch.WordTrace]
  refine ⟨17817569352200946971429869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23756759136267929295239825 17817569352200946971429869)
  ·
    refine ⟨6681588507075355114286201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17817569352200946971429869 6681588507075355114286201)
    ·
      refine ⟨5011191380306516335714651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6681588507075355114286201 5011191380306516335714651)
      ·
        refine ⟨7516787070459774503571977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5011191380306516335714651 7516787070459774503571977)
        ·
          refine ⟨5637590302844830877678983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7516787070459774503571977 5637590302844830877678983)
          ·
            refine ⟨8456385454267246316518475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5637590302844830877678983 8456385454267246316518475)
            ·
              refine ⟨12684578181400869474777713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8456385454267246316518475 12684578181400869474777713)
              ·
                refine ⟨9513433636050652106083285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12684578181400869474777713 9513433636050652106083285)
                ·
                  refine ⟨222971100844937158736327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9513433636050652106083285 222971100844937158736327)
                  ·
                    rfl

theorem cell21_977028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_977028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_977028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_977028 prefixEnd_977028 := by exact prefixLift 977028
  have htrace : WordTrace (prefixWord ++ tailWord_977028) baseStart_977028 baseEnd_977028 := by
    simpa [prefixWord, tailWord_977028, baseEnd_977028] using wordTrace_append hprefix tailTrace_977028
  have hstable : (prefixWord ++ tailWord_977028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977028).length < 2 ^ (prefixWord ++ tailWord_977028).sum := by decide
  have hdescent : baseEnd_977028 < baseStart_977028 := by decide
  rcases family_descends (prefixWord ++ tailWord_977028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977045 : List Nat := [1, 3, 2, 1, 1, 1, 3, 6, 3]
def baseStart_977045 : Nat := 118140960795 + 977045 * 2 ^ 59
def prefixEnd_977045 : Nat := 4983230072969 + 3 ^ 40 * 977045 * 2
def baseEnd_977045 : Nat := 222974980476548906952959

theorem tailTrace_977045 : CollatzResearch.WordTrace tailWord_977045 prefixEnd_977045 222974980476548906952959 := by
  unfold tailWord_977045
  simp only [CollatzResearch.WordTrace]
  refine ⟨35635758745340305846228589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23757172496893537230819059 35635758745340305846228589)
  ·
    refine ⟨13363409529502614692335721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35635758745340305846228589 13363409529502614692335721)
    ·
      refine ⟨10022557147126961019251791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13363409529502614692335721 10022557147126961019251791)
      ·
        refine ⟨15033835720690441528877687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10022557147126961019251791 15033835720690441528877687)
        ·
          refine ⟨22550753581035662293316531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15033835720690441528877687 22550753581035662293316531)
          ·
            refine ⟨33826130371553493439974797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22550753581035662293316531 33826130371553493439974797)
            ·
              refine ⟨12684798889332560039990549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33826130371553493439974797 12684798889332560039990549)
              ·
                refine ⟨594599947937463751874557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12684798889332560039990549 594599947937463751874557)
                ·
                  refine ⟨222974980476548906952959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 594599947937463751874557 222974980476548906952959)
                  ·
                    rfl

theorem cell21_977045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 6, 3].length) (baseStart_977045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_977045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_977045 prefixEnd_977045 := by exact prefixLift 977045
  have htrace : WordTrace (prefixWord ++ tailWord_977045) baseStart_977045 baseEnd_977045 := by
    simpa [prefixWord, tailWord_977045, baseEnd_977045] using wordTrace_append hprefix tailTrace_977045
  have hstable : (prefixWord ++ tailWord_977045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977045).length < 2 ^ (prefixWord ++ tailWord_977045).sum := by decide
  have hdescent : baseEnd_977045 < baseStart_977045 := by decide
  rcases family_descends (prefixWord ++ tailWord_977045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977110 : List Nat := [5, 2, 1, 2, 1, 1, 4, 1, 4]
def baseStart_977110 : Nat := 118140960795 + 977110 * 2 ^ 59
def prefixEnd_977110 : Nat := 4983230072969 + 3 ^ 40 * 977110 * 2
def baseEnd_977110 : Nat := 222989814362123238369493

theorem tailTrace_977110 : CollatzResearch.WordTrace tailWord_977110 prefixEnd_977110 222989814362123238369493 := by
  unfold tailWord_977110
  simp only [CollatzResearch.WordTrace]
  refine ⟨2227383093131551371709049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23758752993403214631563189 2227383093131551371709049)
  ·
    refine ⟨1670537319848663528781787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2227383093131551371709049 1670537319848663528781787)
    ·
      refine ⟨2505805979772995293172681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1670537319848663528781787 2505805979772995293172681)
      ·
        refine ⟨1879354484829746469879511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2505805979772995293172681 1879354484829746469879511)
        ·
          refine ⟨2819031727244619704819267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1879354484829746469879511 2819031727244619704819267)
          ·
            refine ⟨4228547590866929557228901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2819031727244619704819267 4228547590866929557228901)
            ·
              refine ⟨792852673287549291980419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4228547590866929557228901 792852673287549291980419)
              ·
                refine ⟨1189279009931323937970629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 792852673287549291980419 1189279009931323937970629)
                ·
                  refine ⟨222989814362123238369493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1189279009931323937970629 222989814362123238369493)
                  ·
                    rfl

theorem cell21_977110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_977110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_977110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_977110 prefixEnd_977110 := by exact prefixLift 977110
  have htrace : WordTrace (prefixWord ++ tailWord_977110) baseStart_977110 baseEnd_977110 := by
    simpa [prefixWord, tailWord_977110, baseEnd_977110] using wordTrace_append hprefix tailTrace_977110
  have hstable : (prefixWord ++ tailWord_977110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977110).length < 2 ^ (prefixWord ++ tailWord_977110).sum := by decide
  have hdescent : baseEnd_977110 < baseStart_977110 := by decide
  rcases family_descends (prefixWord ++ tailWord_977110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977214 : List Nat := [4, 2, 1, 2, 1, 2, 2, 4, 3]
def baseStart_977214 : Nat := 118140960795 + 977214 * 2 ^ 59
def prefixEnd_977214 : Nat := 4983230072969 + 3 ^ 40 * 977214 * 2
def baseEnd_977214 : Nat := 223013548579042168635947

theorem tailTrace_977214 : CollatzResearch.WordTrace tailWord_977214 prefixEnd_977214 223013548579042168635947 := by
  unfold tailWord_977214
  simp only [CollatzResearch.WordTrace]
  refine ⟨4455240335216005963641337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23761281787818698472753797 4455240335216005963641337)
  ·
    refine ⟨3341430251412004472731003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4455240335216005963641337 3341430251412004472731003)
    ·
      refine ⟨5012145377118006709096505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3341430251412004472731003 5012145377118006709096505)
      ·
        refine ⟨3759109032838505031822379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5012145377118006709096505 3759109032838505031822379)
        ·
          refine ⟨5638663549257757547733569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3759109032838505031822379 5638663549257757547733569)
          ·
            refine ⟨4228997661943318160800177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5638663549257757547733569 4228997661943318160800177)
            ·
              refine ⟨3171748246457488620600133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4228997661943318160800177 3171748246457488620600133)
              ·
                refine ⟨594702796210779116362525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3171748246457488620600133 594702796210779116362525)
                ·
                  refine ⟨223013548579042168635947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 594702796210779116362525 223013548579042168635947)
                  ·
                    rfl

theorem cell21_977214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_977214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_977214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_977214 prefixEnd_977214 := by exact prefixLift 977214
  have htrace : WordTrace (prefixWord ++ tailWord_977214) baseStart_977214 baseEnd_977214 := by
    simpa [prefixWord, tailWord_977214, baseEnd_977214] using wordTrace_append hprefix tailTrace_977214
  have hstable : (prefixWord ++ tailWord_977214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977214).length < 2 ^ (prefixWord ++ tailWord_977214).sum := by decide
  have hdescent : baseEnd_977214 < baseStart_977214 := by decide
  rcases family_descends (prefixWord ++ tailWord_977214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977228 : List Nat := [2, 2, 1, 3, 2, 1, 5, 1, 4]
def baseStart_977228 : Nat := 118140960795 + 977228 * 2 ^ 59
def prefixEnd_977228 : Nat := 4983230072969 + 3 ^ 40 * 977228 * 2
def baseEnd_977228 : Nat := 223016743569781255402585

theorem tailTrace_977228 : CollatzResearch.WordTrace tailWord_977228 prefixEnd_977228 223016743569781255402585 := by
  unfold tailWord_977228
  simp only [CollatzResearch.WordTrace]
  refine ⟨17821216651838664050070169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23761622202451552066760225 17821216651838664050070169)
  ·
    refine ⟨13365912488878998037552627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17821216651838664050070169 13365912488878998037552627)
    ·
      refine ⟨20048868733318497056328941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13365912488878998037552627 20048868733318497056328941)
      ·
        refine ⟨7518325774994436396123353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20048868733318497056328941 7518325774994436396123353)
        ·
          refine ⟨5638744331245827297092515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7518325774994436396123353 5638744331245827297092515)
          ·
            refine ⟨8458116496868740945638773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5638744331245827297092515 8458116496868740945638773)
            ·
              refine ⟨792948421581444463653635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8458116496868740945638773 792948421581444463653635)
              ·
                refine ⟨1189422632372166695480453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 792948421581444463653635 1189422632372166695480453)
                ·
                  refine ⟨223016743569781255402585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1189422632372166695480453 223016743569781255402585)
                  ·
                    rfl

theorem cell21_977228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 1, 4].length) (baseStart_977228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_977228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_977228 prefixEnd_977228 := by exact prefixLift 977228
  have htrace : WordTrace (prefixWord ++ tailWord_977228) baseStart_977228 baseEnd_977228 := by
    simpa [prefixWord, tailWord_977228, baseEnd_977228] using wordTrace_append hprefix tailTrace_977228
  have hstable : (prefixWord ++ tailWord_977228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977228).length < 2 ^ (prefixWord ++ tailWord_977228).sum := by decide
  have hdescent : baseEnd_977228 < baseStart_977228 := by decide
  rcases family_descends (prefixWord ++ tailWord_977228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977287 : List Nat := [1, 1, 4, 2, 2, 1, 3, 3, 4]
def baseStart_977287 : Nat := 118140960795 + 977287 * 2 ^ 59
def prefixEnd_977287 : Nat := 4983230072969 + 3 ^ 40 * 977287 * 2
def baseEnd_977287 : Nat := 223030208173610263919131

theorem tailTrace_977287 : CollatzResearch.WordTrace tailWord_977287 prefixEnd_977287 223030208173610263919131 := by
  unfold tailWord_977287
  simp only [CollatzResearch.WordTrace]
  refine ⟨35644585210463581176538115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23763056806975720784358743 35644585210463581176538115)
  ·
    refine ⟨53466877815695371764807173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35644585210463581176538115 53466877815695371764807173)
    ·
      refine ⟨10025039590442882205901345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53466877815695371764807173 10025039590442882205901345)
      ·
        refine ⟨7518779692832161654426009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10025039590442882205901345 7518779692832161654426009)
        ·
          refine ⟨5639084769624121240819507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7518779692832161654426009 5639084769624121240819507)
          ·
            refine ⟨8458627154436181861229261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5639084769624121240819507 8458627154436181861229261)
            ·
              refine ⟨3171985182913568197960973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8458627154436181861229261 3171985182913568197960973)
              ·
                refine ⟨1189494443592588074235365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3171985182913568197960973 1189494443592588074235365)
                ·
                  refine ⟨223030208173610263919131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1189494443592588074235365 223030208173610263919131)
                  ·
                    rfl

theorem cell21_977287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3, 4].length) (baseStart_977287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_977287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_977287 prefixEnd_977287 := by exact prefixLift 977287
  have htrace : WordTrace (prefixWord ++ tailWord_977287) baseStart_977287 baseEnd_977287 := by
    simpa [prefixWord, tailWord_977287, baseEnd_977287] using wordTrace_append hprefix tailTrace_977287
  have hstable : (prefixWord ++ tailWord_977287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977287).length < 2 ^ (prefixWord ++ tailWord_977287).sum := by decide
  have hdescent : baseEnd_977287 < baseStart_977287 := by decide
  rcases family_descends (prefixWord ++ tailWord_977287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977543 : List Nat := [1, 1, 4, 2, 1, 2, 1, 2, 7]
def baseStart_977543 : Nat := 118140960795 + 977543 * 2 ^ 59
def prefixEnd_977543 : Nat := 4983230072969 + 3 ^ 40 * 977543 * 2
def baseEnd_977543 : Nat := 223088630861410707651941

theorem tailTrace_977543 : CollatzResearch.WordTrace tailWord_977543 prefixEnd_977543 223088630861410707651941 := by
  unfold tailWord_977543
  simp only [CollatzResearch.WordTrace]
  refine ⟨35653922297536136897857283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23769281531690757931904855 35653922297536136897857283)
  ·
    refine ⟨53480883446304205346785925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35653922297536136897857283 53480883446304205346785925)
    ·
      refine ⟨10027665646182038502522361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53480883446304205346785925 10027665646182038502522361)
      ·
        refine ⟨7520749234636528876891771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10027665646182038502522361 7520749234636528876891771)
        ·
          refine ⟨11281123851954793315337657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7520749234636528876891771 11281123851954793315337657)
          ·
            refine ⟨8460842888966094986503243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11281123851954793315337657 8460842888966094986503243)
            ·
              refine ⟨12691264333449142479754865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8460842888966094986503243 12691264333449142479754865)
              ·
                refine ⟨9518448250086856859816149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12691264333449142479754865 9518448250086856859816149)
                ·
                  refine ⟨223088630861410707651941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9518448250086856859816149 223088630861410707651941)
                  ·
                    rfl

theorem cell21_977543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 7].length) (baseStart_977543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_977543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_977543 prefixEnd_977543 := by exact prefixLift 977543
  have htrace : WordTrace (prefixWord ++ tailWord_977543) baseStart_977543 baseEnd_977543 := by
    simpa [prefixWord, tailWord_977543, baseEnd_977543] using wordTrace_append hprefix tailTrace_977543
  have hstable : (prefixWord ++ tailWord_977543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977543).length < 2 ^ (prefixWord ++ tailWord_977543).sum := by decide
  have hdescent : baseEnd_977543 < baseStart_977543 := by decide
  rcases family_descends (prefixWord ++ tailWord_977543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977560 : List Nat := [2, 1, 2, 4, 1, 1, 4, 1, 5]
def baseStart_977560 : Nat := 118140960795 + 977560 * 2 ^ 59
def prefixEnd_977560 : Nat := 4983230072969 + 3 ^ 40 * 977560 * 2
def baseEnd_977560 : Nat := 223092510493022455868573

theorem tailTrace_977560 : CollatzResearch.WordTrace tailWord_977560 prefixEnd_977560 223092510493022455868573 := by
  unfold tailWord_977560
  simp only [CollatzResearch.WordTrace]
  refine ⟨17827271169237274400613067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23769694892316365867484089 17827271169237274400613067)
  ·
    refine ⟨26740906753855911600919601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17827271169237274400613067 26740906753855911600919601)
    ·
      refine ⟨20055680065391933700689701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26740906753855911600919601 20055680065391933700689701)
      ·
        refine ⟨3760440012260987568879319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20055680065391933700689701 3760440012260987568879319)
        ·
          refine ⟨5640660018391481353318979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3760440012260987568879319 5640660018391481353318979)
          ·
            refine ⟨8460990027587222029978469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5640660018391481353318979 8460990027587222029978469)
            ·
              refine ⟨1586435630172604130620963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8460990027587222029978469 1586435630172604130620963)
              ·
                refine ⟨2379653445258906195931445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1586435630172604130620963 2379653445258906195931445)
                ·
                  refine ⟨223092510493022455868573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2379653445258906195931445 223092510493022455868573)
                  ·
                    rfl

theorem cell21_977560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 5].length) (baseStart_977560 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_977560 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_977560 prefixEnd_977560 := by exact prefixLift 977560
  have htrace : WordTrace (prefixWord ++ tailWord_977560) baseStart_977560 baseEnd_977560 := by
    simpa [prefixWord, tailWord_977560, baseEnd_977560] using wordTrace_append hprefix tailTrace_977560
  have hstable : (prefixWord ++ tailWord_977560).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977560).length < 2 ^ (prefixWord ++ tailWord_977560).sum := by decide
  have hdescent : baseEnd_977560 < baseStart_977560 := by decide
  rcases family_descends (prefixWord ++ tailWord_977560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977695 : List Nat := [1, 1, 2, 4, 2, 2, 1, 1, 7]
def baseStart_977695 : Nat := 118140960795 + 977695 * 2 ^ 59
def prefixEnd_977695 : Nat := 4983230072969 + 3 ^ 40 * 977695 * 2
def baseEnd_977695 : Nat := 223123319332292221118297

theorem tailTrace_977695 : CollatzResearch.WordTrace tailWord_977695 prefixEnd_977695 223123319332292221118297 := by
  unfold tailWord_977695
  simp only [CollatzResearch.WordTrace]
  refine ⟨35659466192985466857390539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23772977461990311238260359 35659466192985466857390539)
  ·
    refine ⟨53489199289478200286085809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35659466192985466857390539 53489199289478200286085809)
    ·
      refine ⟨40116899467108650214564357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53489199289478200286085809 40116899467108650214564357)
      ·
        refine ⟨7521918650082871915230817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40116899467108650214564357 7521918650082871915230817)
        ·
          refine ⟨5641438987562153936423113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7521918650082871915230817 5641438987562153936423113)
          ·
            refine ⟨4231079240671615452317335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5641438987562153936423113 4231079240671615452317335)
            ·
              refine ⟨6346618861007423178476003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4231079240671615452317335 6346618861007423178476003)
              ·
                refine ⟨9519928291511134767714005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6346618861007423178476003 9519928291511134767714005)
                ·
                  refine ⟨223123319332292221118297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9519928291511134767714005 223123319332292221118297)
                  ·
                    rfl

theorem cell21_977695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 7].length) (baseStart_977695 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_977695 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_977695 prefixEnd_977695 := by exact prefixLift 977695
  have htrace : WordTrace (prefixWord ++ tailWord_977695) baseStart_977695 baseEnd_977695 := by
    simpa [prefixWord, tailWord_977695, baseEnd_977695] using wordTrace_append hprefix tailTrace_977695
  have hstable : (prefixWord ++ tailWord_977695).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977695).length < 2 ^ (prefixWord ++ tailWord_977695).sum := by decide
  have hdescent : baseEnd_977695 < baseStart_977695 := by decide
  rcases family_descends (prefixWord ++ tailWord_977695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977698 : List Nat := [3, 3, 1, 1, 2, 3, 3, 5]
def baseStart_977698 : Nat := 118140960795 + 977698 * 2 ^ 59
def prefixEnd_977698 : Nat := 4983230072969 + 3 ^ 40 * 977698 * 2
def baseEnd_977698 : Nat := 74374667991054960856097

theorem tailTrace_977698 : CollatzResearch.WordTrace tailWord_977698 prefixEnd_977698 74374667991054960856097 := by
  unfold tailWord_977698
  simp only [CollatzResearch.WordTrace]
  refine ⟨8914893902993649592437437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23773050407983065579833165 8914893902993649592437437)
  ·
    refine ⟨3343085213622618597164039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8914893902993649592437437 3343085213622618597164039)
    ·
      refine ⟨5014627820433927895746059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3343085213622618597164039 5014627820433927895746059)
      ·
        refine ⟨7521941730650891843619089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5014627820433927895746059 7521941730650891843619089)
        ·
          refine ⟨5641456297988168882714317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7521941730650891843619089 5641456297988168882714317)
          ·
            refine ⟨2115546111745563331017869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5641456297988168882714317 2115546111745563331017869)
            ·
              refine ⟨793329791904586249131701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2115546111745563331017869 793329791904586249131701)
              ·
                refine ⟨74374667991054960856097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 793329791904586249131701 74374667991054960856097)
                ·
                  rfl

theorem cell21_977698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 5].length) (baseStart_977698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_977698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_977698 prefixEnd_977698 := by exact prefixLift 977698
  have htrace : WordTrace (prefixWord ++ tailWord_977698) baseStart_977698 baseEnd_977698 := by
    simpa [prefixWord, tailWord_977698, baseEnd_977698] using wordTrace_append hprefix tailTrace_977698
  have hstable : (prefixWord ++ tailWord_977698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977698).length < 2 ^ (prefixWord ++ tailWord_977698).sum := by decide
  have hdescent : baseEnd_977698 < baseStart_977698 := by decide
  rcases family_descends (prefixWord ++ tailWord_977698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977718 : List Nat := [5, 1, 2, 2, 3, 1, 1, 2, 4]
def baseStart_977718 : Nat := 118140960795 + 977718 * 2 ^ 59
def prefixEnd_977718 : Nat := 4983230072969 + 3 ^ 40 * 977718 * 2
def baseEnd_977718 : Nat := 223128568245649292234917

theorem tailTrace_977718 : CollatzResearch.WordTrace tailWord_977718 prefixEnd_977718 223128568245649292234917 := by
  unfold tailWord_977718
  simp only [CollatzResearch.WordTrace]
  refine ⟨2228769066993883861592363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23773536714601427856985205 2228769066993883861592363)
  ·
    refine ⟨3343153600490825792388545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2228769066993883861592363 3343153600490825792388545)
    ·
      refine ⟨2507365200368119344291409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3343153600490825792388545 2507365200368119344291409)
      ·
        refine ⟨1880523900276089508218557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2507365200368119344291409 1880523900276089508218557)
        ·
          refine ⟨705196462603533565581959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1880523900276089508218557 705196462603533565581959)
          ·
            refine ⟨1057794693905300348372939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 705196462603533565581959 1057794693905300348372939)
            ·
              refine ⟨1586692040857950522559409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1057794693905300348372939 1586692040857950522559409)
              ·
                refine ⟨1190019030643462891919557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1586692040857950522559409 1190019030643462891919557)
                ·
                  refine ⟨223128568245649292234917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1190019030643462891919557 223128568245649292234917)
                  ·
                    rfl

theorem cell21_977718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_977718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_977718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_977718 prefixEnd_977718 := by exact prefixLift 977718
  have htrace : WordTrace (prefixWord ++ tailWord_977718) baseStart_977718 baseEnd_977718 := by
    simpa [prefixWord, tailWord_977718, baseEnd_977718] using wordTrace_append hprefix tailTrace_977718
  have hstable : (prefixWord ++ tailWord_977718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977718).length < 2 ^ (prefixWord ++ tailWord_977718).sum := by decide
  have hdescent : baseEnd_977718 < baseStart_977718 := by decide
  rcases family_descends (prefixWord ++ tailWord_977718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977774 : List Nat := [4, 1, 2, 3, 2, 2, 7]
def baseStart_977774 : Nat := 118140960795 + 977774 * 2 ^ 59
def prefixEnd_977774 : Nat := 4983230072969 + 3 ^ 40 * 977774 * 2
def baseEnd_977774 : Nat := 24793483134289515477941

theorem tailTrace_977774 : CollatzResearch.WordTrace tailWord_977774 prefixEnd_977774 24793483134289515477941 := by
  unfold tailWord_977774
  simp only [CollatzResearch.WordTrace]
  refine ⟨4457793444962407918689547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23774898373132842233010917 4457793444962407918689547)
  ·
    refine ⟨6686690167443611878034321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4457793444962407918689547 6686690167443611878034321)
    ·
      refine ⟨5015017625582708908525741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6686690167443611878034321 5015017625582708908525741)
      ·
        refine ⟨1880631609593515840697153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5015017625582708908525741 1880631609593515840697153)
        ·
          refine ⟨1410473707195136880522865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1880631609593515840697153 1410473707195136880522865)
          ·
            refine ⟨1057855280396352660392149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1410473707195136880522865 1057855280396352660392149)
            ·
              refine ⟨24793483134289515477941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1057855280396352660392149 24793483134289515477941)
              ·
                rfl

theorem cell21_977774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 7].length) (baseStart_977774 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_977774 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_977774 prefixEnd_977774 := by exact prefixLift 977774
  have htrace : WordTrace (prefixWord ++ tailWord_977774) baseStart_977774 baseEnd_977774 := by
    simpa [prefixWord, tailWord_977774, baseEnd_977774] using wordTrace_append hprefix tailTrace_977774
  have hstable : (prefixWord ++ tailWord_977774).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977774).length < 2 ^ (prefixWord ++ tailWord_977774).sum := by decide
  have hdescent : baseEnd_977774 < baseStart_977774 := by decide
  rcases family_descends (prefixWord ++ tailWord_977774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977788 : List Nat := [2, 2, 2, 1, 1, 1, 1, 8, 3]
def baseStart_977788 : Nat := 118140960795 + 977788 * 2 ^ 59
def prefixEnd_977788 : Nat := 4983230072969 + 3 ^ 40 * 977788 * 2
def baseEnd_977788 : Nat := 223144543199344726068107

theorem tailTrace_977788 : CollatzResearch.WordTrace tailWord_977788 prefixEnd_977788 223144543199344726068107 := by
  unfold tailWord_977788
  simp only [CollatzResearch.WordTrace]
  refine ⟨17831429090824271870263009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23775238787765695827017345 17831429090824271870263009)
  ·
    refine ⟨13373571818118203902697257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17831429090824271870263009 13373571818118203902697257)
    ·
      refine ⟨10030178863588652927022943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13373571818118203902697257 10030178863588652927022943)
      ·
        refine ⟨15045268295382979390534415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10030178863588652927022943 15045268295382979390534415)
        ·
          refine ⟨22567902443074469085801623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15045268295382979390534415 22567902443074469085801623)
          ·
            refine ⟨33851853664611703628702435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22567902443074469085801623 33851853664611703628702435)
            ·
              refine ⟨50777780496917555443053653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33851853664611703628702435 50777780496917555443053653)
              ·
                refine ⟨595052115198252602848285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 50777780496917555443053653 595052115198252602848285)
                ·
                  refine ⟨223144543199344726068107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 595052115198252602848285 223144543199344726068107)
                  ·
                    rfl

theorem cell21_977788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 8, 3].length) (baseStart_977788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_977788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_977788 prefixEnd_977788 := by exact prefixLift 977788
  have htrace : WordTrace (prefixWord ++ tailWord_977788) baseStart_977788 baseEnd_977788 := by
    simpa [prefixWord, tailWord_977788, baseEnd_977788] using wordTrace_append hprefix tailTrace_977788
  have hstable : (prefixWord ++ tailWord_977788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977788).length < 2 ^ (prefixWord ++ tailWord_977788).sum := by decide
  have hdescent : baseEnd_977788 < baseStart_977788 := by decide
  rcases family_descends (prefixWord ++ tailWord_977788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977864 : List Nat := [2, 1, 3, 1, 5, 1, 1, 2, 5]
def baseStart_977864 : Nat := 118140960795 + 977864 * 2 ^ 59
def prefixEnd_977864 : Nat := 4983230072969 + 3 ^ 40 * 977864 * 2
def baseEnd_977864 : Nat := 223161887434785482801285

theorem tailTrace_977864 : CollatzResearch.WordTrace tailWord_977864 prefixEnd_977864 223161887434785482801285 := by
  unfold tailWord_977864
  simp only [CollatzResearch.WordTrace]
  refine ⟨17832815064686604360146323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23777086752915472480195097 17832815064686604360146323)
  ·
    refine ⟨26749222597029906540219485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17832815064686604360146323 26749222597029906540219485)
    ·
      refine ⟨10030958473886214952582307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26749222597029906540219485 10030958473886214952582307)
      ·
        refine ⟨15046437710829322428873461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10030958473886214952582307 15046437710829322428873461)
        ·
          refine ⟨1410603535390248977706887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15046437710829322428873461 1410603535390248977706887)
          ·
            refine ⟨2115905303085373466560331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1410603535390248977706887 2115905303085373466560331)
            ·
              refine ⟨3173857954628060199840497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2115905303085373466560331 3173857954628060199840497)
              ·
                refine ⟨2380393465971045149880373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3173857954628060199840497 2380393465971045149880373)
                ·
                  refine ⟨223161887434785482801285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2380393465971045149880373 223161887434785482801285)
                  ·
                    rfl

theorem cell21_977864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 5].length) (baseStart_977864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_977864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_977864 prefixEnd_977864 := by exact prefixLift 977864
  have htrace : WordTrace (prefixWord ++ tailWord_977864) baseStart_977864 baseEnd_977864 := by
    simpa [prefixWord, tailWord_977864, baseEnd_977864] using wordTrace_append hprefix tailTrace_977864
  have hstable : (prefixWord ++ tailWord_977864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977864).length < 2 ^ (prefixWord ++ tailWord_977864).sum := by decide
  have hdescent : baseEnd_977864 < baseStart_977864 := by decide
  rcases family_descends (prefixWord ++ tailWord_977864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977881 : List Nat := [1, 2, 1, 2, 5, 2, 2, 3, 3]
def baseStart_977881 : Nat := 118140960795 + 977881 * 2 ^ 59
def prefixEnd_977881 : Nat := 4983230072969 + 3 ^ 40 * 977881 * 2
def baseEnd_977881 : Nat := 223165767066397231017917

theorem tailTrace_977881 : CollatzResearch.WordTrace tailWord_977881 prefixEnd_977881 223165767066397231017917 := by
  unfold tailWord_977881
  simp only [CollatzResearch.WordTrace]
  refine ⟨35666250170311620623661497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23777500113541080415774331 35666250170311620623661497)
  ·
    refine ⟨26749687627733715467746123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35666250170311620623661497 26749687627733715467746123)
    ·
      refine ⟨40124531441600573201619185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26749687627733715467746123 40124531441600573201619185)
      ·
        refine ⟨30093398581200429901214389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40124531441600573201619185 30093398581200429901214389)
        ·
          refine ⟨2821256116987540303238849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30093398581200429901214389 2821256116987540303238849)
          ·
            refine ⟨2115942087740655227429137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2821256116987540303238849 2115942087740655227429137)
            ·
              refine ⟨1586956565805491420571853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2115942087740655227429137 1586956565805491420571853)
              ·
                refine ⟨595108712177059282714445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1586956565805491420571853 595108712177059282714445)
                ·
                  refine ⟨223165767066397231017917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 595108712177059282714445 223165767066397231017917)
                  ·
                    rfl

theorem cell21_977881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 3, 3].length) (baseStart_977881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_977881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_977881 prefixEnd_977881 := by exact prefixLift 977881
  have htrace : WordTrace (prefixWord ++ tailWord_977881) baseStart_977881 baseEnd_977881 := by
    simpa [prefixWord, tailWord_977881, baseEnd_977881] using wordTrace_append hprefix tailTrace_977881
  have hstable : (prefixWord ++ tailWord_977881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977881).length < 2 ^ (prefixWord ++ tailWord_977881).sum := by decide
  have hdescent : baseEnd_977881 < baseStart_977881 := by decide
  rcases family_descends (prefixWord ++ tailWord_977881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977895 : List Nat := [1, 1, 5, 2, 2, 1, 3, 2, 4]
def baseStart_977895 : Nat := 118140960795 + 977895 * 2 ^ 59
def prefixEnd_977895 : Nat := 4983230072969 + 3 ^ 40 * 977895 * 2
def baseEnd_977895 : Nat := 223168962057136317784555

theorem tailTrace_977895 : CollatzResearch.WordTrace tailWord_977895 prefixEnd_977895 223168962057136317784555 := by
  unfold tailWord_977895
  simp only [CollatzResearch.WordTrace]
  refine ⟨35666760792260901014671139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23777840528173934009780759 35666760792260901014671139)
  ·
    refine ⟨53500141188391351522006709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35666760792260901014671139 53500141188391351522006709)
    ·
      refine ⟨5015638236411689205188129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53500141188391351522006709 5015638236411689205188129)
      ·
        refine ⟨3761728677308766903891097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5015638236411689205188129 3761728677308766903891097)
        ·
          refine ⟨2821296507981575177918323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3761728677308766903891097 2821296507981575177918323)
          ·
            refine ⟨4231944761972362766877485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2821296507981575177918323 4231944761972362766877485)
            ·
              refine ⟨1586979285739636037579057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4231944761972362766877485 1586979285739636037579057)
              ·
                refine ⟨1190234464304727028184293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1586979285739636037579057 1190234464304727028184293)
                ·
                  refine ⟨223168962057136317784555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1190234464304727028184293 223168962057136317784555)
                  ·
                    rfl

theorem cell21_977895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2, 4].length) (baseStart_977895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_977895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_977895 prefixEnd_977895 := by exact prefixLift 977895
  have htrace : WordTrace (prefixWord ++ tailWord_977895) baseStart_977895 baseEnd_977895 := by
    simpa [prefixWord, tailWord_977895, baseEnd_977895] using wordTrace_append hprefix tailTrace_977895
  have hstable : (prefixWord ++ tailWord_977895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977895).length < 2 ^ (prefixWord ++ tailWord_977895).sum := by decide
  have hdescent : baseEnd_977895 < baseStart_977895 := by decide
  rcases family_descends (prefixWord ++ tailWord_977895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977954 : List Nat := [3, 3, 1, 1, 1, 3, 2, 1, 6]
def baseStart_977954 : Nat := 118140960795 + 977954 * 2 ^ 59
def prefixEnd_977954 : Nat := 4983230072969 + 3 ^ 40 * 977954 * 2
def baseEnd_977954 : Nat := 223182426660965326301101

theorem tailTrace_977954 : CollatzResearch.WordTrace tailWord_977954 prefixEnd_977954 223182426660965326301101 := by
  unfold tailWord_977954
  simp only [CollatzResearch.WordTrace]
  refine ⟨8917228174761788522767229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23779275132698102727379277 8917228174761788522767229)
  ·
    refine ⟨3343960565535670696037711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8917228174761788522767229 3343960565535670696037711)
    ·
      refine ⟨5015940848303506044056567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3343960565535670696037711 5015940848303506044056567)
      ·
        refine ⟨7523911272455259066084851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5015940848303506044056567 7523911272455259066084851)
        ·
          refine ⟨11285866908682888599127277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7523911272455259066084851 11285866908682888599127277)
          ·
            refine ⟨4232200090756083224672729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11285866908682888599127277 4232200090756083224672729)
            ·
              refine ⟨3174150068067062418504547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4232200090756083224672729 3174150068067062418504547)
              ·
                refine ⟨4761225102100593627756821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3174150068067062418504547 4761225102100593627756821)
                ·
                  refine ⟨223182426660965326301101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4761225102100593627756821 223182426660965326301101)
                  ·
                    rfl

theorem cell21_977954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_977954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_977954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_977954 prefixEnd_977954 := by exact prefixLift 977954
  have htrace : WordTrace (prefixWord ++ tailWord_977954) baseStart_977954 baseEnd_977954 := by
    simpa [prefixWord, tailWord_977954, baseEnd_977954] using wordTrace_append hprefix tailTrace_977954
  have hstable : (prefixWord ++ tailWord_977954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977954).length < 2 ^ (prefixWord ++ tailWord_977954).sum := by decide
  have hdescent : baseEnd_977954 < baseStart_977954 := by decide
  rcases family_descends (prefixWord ++ tailWord_977954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977957 : List Nat := [1, 3, 1, 2, 2, 2, 5, 2, 3]
def baseStart_977957 : Nat := 118140960795 + 977957 * 2 ^ 59
def prefixEnd_977957 : Nat := 4983230072969 + 3 ^ 40 * 977957 * 2
def baseEnd_977957 : Nat := 223183111301837987751095

theorem tailTrace_977957 : CollatzResearch.WordTrace tailWord_977957 prefixEnd_977957 223183111301837987751095 := by
  unfold tailWord_977957
  simp only [CollatzResearch.WordTrace]
  refine ⟨35669022118036285603428125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23779348078690857068952083 35669022118036285603428125)
  ·
    refine ⟨13375883294263607101285547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35669022118036285603428125 13375883294263607101285547)
    ·
      refine ⟨20063824941395410651928321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13375883294263607101285547 20063824941395410651928321)
      ·
        refine ⟨15047868706046557988946241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20063824941395410651928321 15047868706046557988946241)
        ·
          refine ⟨11285901529534918491709681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15047868706046557988946241 11285901529534918491709681)
          ·
            refine ⟨8464426147151188868782261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11285901529534918491709681 8464426147151188868782261)
            ·
              refine ⟨793539951295423956448337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8464426147151188868782261 793539951295423956448337)
              ·
                refine ⟨595154963471567967336253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 793539951295423956448337 595154963471567967336253)
                ·
                  refine ⟨223183111301837987751095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 595154963471567967336253 223183111301837987751095)
                  ·
                    rfl

theorem cell21_977957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 2, 3].length) (baseStart_977957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_977957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_977957 prefixEnd_977957 := by exact prefixLift 977957
  have htrace : WordTrace (prefixWord ++ tailWord_977957) baseStart_977957 baseEnd_977957 := by
    simpa [prefixWord, tailWord_977957, baseEnd_977957] using wordTrace_append hprefix tailTrace_977957
  have hstable : (prefixWord ++ tailWord_977957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977957).length < 2 ^ (prefixWord ++ tailWord_977957).sum := by decide
  have hdescent : baseEnd_977957 < baseStart_977957 := by decide
  rcases family_descends (prefixWord ++ tailWord_977957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977968 : List Nat := [2, 1, 1, 1, 2, 4, 4, 6]
def baseStart_977968 : Nat := 118140960795 + 977968 * 2 ^ 59
def prefixEnd_977968 : Nat := 4983230072969 + 3 ^ 40 * 977968 * 2
def baseEnd_977968 : Nat := 74395207217234804355913

theorem tailTrace_977968 : CollatzResearch.WordTrace tailWord_977968 prefixEnd_977968 74395207217234804355913 := by
  unfold tailWord_977968
  simp only [CollatzResearch.WordTrace]
  refine ⟨17834711660498217241039279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23779615547330956321385705 17834711660498217241039279)
  ·
    refine ⟨26752067490747325861558919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17834711660498217241039279 26752067490747325861558919)
    ·
      refine ⟨40128101236120988792338379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26752067490747325861558919 40128101236120988792338379)
      ·
        refine ⟨60192151854181483188507569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40128101236120988792338379 60192151854181483188507569)
        ·
          refine ⟨45144113890636112391380677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60192151854181483188507569 45144113890636112391380677)
          ·
            refine ⟨8464521354494271073383877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45144113890636112391380677 8464521354494271073383877)
            ·
              refine ⟨1587097753967675826259477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8464521354494271073383877 1587097753967675826259477)
              ·
                refine ⟨74395207217234804355913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1587097753967675826259477 74395207217234804355913)
                ·
                  rfl

theorem cell21_977968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 6].length) (baseStart_977968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_977968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_977968 prefixEnd_977968 := by exact prefixLift 977968
  have htrace : WordTrace (prefixWord ++ tailWord_977968) baseStart_977968 baseEnd_977968 := by
    simpa [prefixWord, tailWord_977968, baseEnd_977968] using wordTrace_append hprefix tailTrace_977968
  have hstable : (prefixWord ++ tailWord_977968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977968).length < 2 ^ (prefixWord ++ tailWord_977968).sum := by decide
  have hdescent : baseEnd_977968 < baseStart_977968 := by decide
  rcases family_descends (prefixWord ++ tailWord_977968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978016 : List Nat := [2, 1, 1, 3, 2, 2, 3, 4, 3]
def baseStart_978016 : Nat := 118140960795 + 978016 * 2 ^ 59
def prefixEnd_978016 : Nat := 4983230072969 + 3 ^ 40 * 978016 * 2
def baseEnd_978016 : Nat := 223196575905666996267641

theorem tailTrace_978016 : CollatzResearch.WordTrace tailWord_978016 prefixEnd_978016 223196575905666996267641 := by
  unfold tailWord_978016
  simp only [CollatzResearch.WordTrace]
  refine ⟨17835587012411269339912951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23780782683215025786550601 17835587012411269339912951)
  ·
    refine ⟨26753380518616904009869427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17835587012411269339912951 26753380518616904009869427)
    ·
      refine ⟨40130070777925356014804141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26753380518616904009869427 40130070777925356014804141)
      ·
        refine ⟨15048776541722008505551553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40130070777925356014804141 15048776541722008505551553)
        ·
          refine ⟨11286582406291506379163665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15048776541722008505551553 11286582406291506379163665)
          ·
            refine ⟨8464936804718629784372749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11286582406291506379163665 8464936804718629784372749)
            ·
              refine ⟨3174351301769486169139781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8464936804718629784372749 3174351301769486169139781)
              ·
                refine ⟨595190869081778656713709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3174351301769486169139781 595190869081778656713709)
                ·
                  refine ⟨223196575905666996267641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 595190869081778656713709 223196575905666996267641)
                  ·
                    rfl

theorem cell21_978016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 4, 3].length) (baseStart_978016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_978016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_978016 prefixEnd_978016 := by exact prefixLift 978016
  have htrace : WordTrace (prefixWord ++ tailWord_978016) baseStart_978016 baseEnd_978016 := by
    simpa [prefixWord, tailWord_978016, baseEnd_978016] using wordTrace_append hprefix tailTrace_978016
  have hstable : (prefixWord ++ tailWord_978016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978016).length < 2 ^ (prefixWord ++ tailWord_978016).sum := by decide
  have hdescent : baseEnd_978016 < baseStart_978016 := by decide
  rcases family_descends (prefixWord ++ tailWord_978016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978126 : List Nat := [4, 1, 1, 1, 5, 1, 3, 2, 3]
def baseStart_978126 : Nat := 118140960795 + 978126 * 2 ^ 59
def prefixEnd_978126 : Nat := 4983230072969 + 3 ^ 40 * 978126 * 2
def baseEnd_978126 : Nat := 223221679404331249434083

theorem tailTrace_978126 : CollatzResearch.WordTrace tailWord_978126 prefixEnd_978126 223221679404331249434083 := by
  unfold tailWord_978126
  simp only [CollatzResearch.WordTrace]
  refine ⟨4459398256803003433291279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23783457369616018310886821 4459398256803003433291279)
  ·
    refine ⟨6689097385204505149936919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4459398256803003433291279 6689097385204505149936919)
    ·
      refine ⟨10033646077806757724905379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6689097385204505149936919 10033646077806757724905379)
      ·
        refine ⟨15050469116710136587358069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10033646077806757724905379 15050469116710136587358069)
        ·
          refine ⟨1410981479691575305064819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15050469116710136587358069 1410981479691575305064819)
          ·
            refine ⟨2116472219537362957597229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1410981479691575305064819 2116472219537362957597229)
            ·
              refine ⟨793677082326511109098961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2116472219537362957597229 793677082326511109098961)
              ·
                refine ⟨595257811744883331824221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 793677082326511109098961 595257811744883331824221)
                ·
                  refine ⟨223221679404331249434083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 595257811744883331824221 223221679404331249434083)
                  ·
                    rfl

theorem cell21_978126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 2, 3].length) (baseStart_978126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_978126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_978126 prefixEnd_978126 := by exact prefixLift 978126
  have htrace : WordTrace (prefixWord ++ tailWord_978126) baseStart_978126 baseEnd_978126 := by
    simpa [prefixWord, tailWord_978126, baseEnd_978126] using wordTrace_append hprefix tailTrace_978126
  have hstable : (prefixWord ++ tailWord_978126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978126).length < 2 ^ (prefixWord ++ tailWord_978126).sum := by decide
  have hdescent : baseEnd_978126 < baseStart_978126 := by decide
  rcases family_descends (prefixWord ++ tailWord_978126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978179 : List Nat := [1, 1, 1, 3, 2, 13]
def baseStart_978179 : Nat := 118140960795 + 978179 * 2 ^ 59
def prefixEnd_978179 : Nat := 4983230072969 + 3 ^ 40 * 978179 * 2
def baseEnd_978179 : Nat := 8267917582459812409283

theorem tailTrace_978179 : CollatzResearch.WordTrace tailWord_978179 prefixEnd_978179 8267917582459812409283 := by
  unfold tailWord_978179
  simp only [CollatzResearch.WordTrace]
  refine ⟨35677119123232017518009591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23784746082154678345339727 35677119123232017518009591)
  ·
    refine ⟨53515678684848026277014387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35677119123232017518009591 53515678684848026277014387)
    ·
      refine ⟨80273518027272039415521581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53515678684848026277014387 80273518027272039415521581)
      ·
        refine ⟨30102569260227014780820593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80273518027272039415521581 30102569260227014780820593)
        ·
          refine ⟨22576926945170261085615445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30102569260227014780820593 22576926945170261085615445)
          ·
            refine ⟨8267917582459812409283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 22576926945170261085615445 8267917582459812409283)
            ·
              rfl

theorem cell21_978179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 13].length) (baseStart_978179 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_978179 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_978179 prefixEnd_978179 := by exact prefixLift 978179
  have htrace : WordTrace (prefixWord ++ tailWord_978179) baseStart_978179 baseEnd_978179 := by
    simpa [prefixWord, tailWord_978179, baseEnd_978179] using wordTrace_append hprefix tailTrace_978179
  have hstable : (prefixWord ++ tailWord_978179).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978179).length < 2 ^ (prefixWord ++ tailWord_978179).sum := by decide
  have hdescent : baseEnd_978179 < baseStart_978179 := by decide
  rcases family_descends (prefixWord ++ tailWord_978179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978213 : List Nat := [1, 3, 1, 2, 4, 2, 3, 5]
def baseStart_978213 : Nat := 118140960795 + 978213 * 2 ^ 59
def prefixEnd_978213 : Nat := 4983230072969 + 3 ^ 40 * 978213 * 2
def baseEnd_978213 : Nat := 74413844663212810494635

theorem tailTrace_978213 : CollatzResearch.WordTrace tailWord_978213 prefixEnd_978213 74413844663212810494635 := by
  unfold tailWord_978213
  simp only [CollatzResearch.WordTrace]
  refine ⟨35678359205108841324747293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23785572803405894216498195 35678359205108841324747293)
  ·
    refine ⟨13379384701915815496780235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35678359205108841324747293 13379384701915815496780235)
    ·
      refine ⟨20069077052873723245170353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13379384701915815496780235 20069077052873723245170353)
      ·
        refine ⟨15051807789655292433877765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20069077052873723245170353 15051807789655292433877765)
        ·
          refine ⟨2822213960560367331352081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15051807789655292433877765 2822213960560367331352081)
          ·
            refine ⟨2116660470420275498514061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2822213960560367331352081 2116660470420275498514061)
            ·
              refine ⟨793747676407603311942773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2116660470420275498514061 793747676407603311942773)
              ·
                refine ⟨74413844663212810494635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 793747676407603311942773 74413844663212810494635)
                ·
                  rfl

theorem cell21_978213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 5].length) (baseStart_978213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_978213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_978213 prefixEnd_978213 := by exact prefixLift 978213
  have htrace : WordTrace (prefixWord ++ tailWord_978213) baseStart_978213 baseEnd_978213 := by
    simpa [prefixWord, tailWord_978213, baseEnd_978213] using wordTrace_append hprefix tailTrace_978213
  have hstable : (prefixWord ++ tailWord_978213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978213).length < 2 ^ (prefixWord ++ tailWord_978213).sum := by decide
  have hdescent : baseEnd_978213 < baseStart_978213 := by decide
  rcases family_descends (prefixWord ++ tailWord_978213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978230 : List Nat := [5, 1, 2, 3, 1, 1, 8]
def baseStart_978230 : Nat := 118140960795 + 978230 * 2 ^ 59
def prefixEnd_978230 : Nat := 4983230072969 + 3 ^ 40 * 978230 * 2
def baseEnd_978230 : Nat := 24805045957916686633393

theorem tailTrace_978230 : CollatzResearch.WordTrace tailWord_978230 prefixEnd_978230 24805045957916686633393 := by
  unfold tailWord_978230
  simp only [CollatzResearch.WordTrace]
  refine ⟨2229936202877953326757259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23785986164031502152077429 2229936202877953326757259)
  ·
    refine ⟨3344904304316929990135889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2229936202877953326757259 3344904304316929990135889)
    ·
      refine ⟨2508678228237697492601917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3344904304316929990135889 2508678228237697492601917)
      ·
        refine ⟨940754335589136559725719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2508678228237697492601917 940754335589136559725719)
        ·
          refine ⟨1411131503383704839588579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 940754335589136559725719 1411131503383704839588579)
          ·
            refine ⟨2116697255075557259382869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1411131503383704839588579 2116697255075557259382869)
            ·
              refine ⟨24805045957916686633393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2116697255075557259382869 24805045957916686633393)
              ·
                rfl

theorem cell21_978230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 8].length) (baseStart_978230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_978230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_978230 prefixEnd_978230 := by exact prefixLift 978230
  have htrace : WordTrace (prefixWord ++ tailWord_978230) baseStart_978230 baseEnd_978230 := by
    simpa [prefixWord, tailWord_978230, baseEnd_978230] using wordTrace_append hprefix tailTrace_978230
  have hstable : (prefixWord ++ tailWord_978230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978230).length < 2 ^ (prefixWord ++ tailWord_978230).sum := by decide
  have hdescent : baseEnd_978230 < baseStart_978230 := by decide
  rcases family_descends (prefixWord ++ tailWord_978230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978244 : List Nat := [2, 3, 4, 1, 1, 1, 1, 3, 5]
def baseStart_978244 : Nat := 118140960795 + 978244 * 2 ^ 59
def prefixEnd_978244 : Nat := 4983230072969 + 3 ^ 40 * 978244 * 2
def baseEnd_978244 : Nat := 223248608611989266467175

theorem tailTrace_978244 : CollatzResearch.WordTrace tailWord_978244 prefixEnd_978244 223248608611989266467175 := by
  unfold tailWord_978244
  simp only [CollatzResearch.WordTrace]
  refine ⟨17839744933998266809562893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23786326578664355746083857 17839744933998266809562893)
  ·
    refine ⟨6689904350249350053586085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17839744933998266809562893 6689904350249350053586085)
    ·
      refine ⟨1254357065671753135047391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6689904350249350053586085 1254357065671753135047391)
      ·
        refine ⟨1881535598507629702571087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1254357065671753135047391 1881535598507629702571087)
        ·
          refine ⟨2822303397761444553856631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1881535598507629702571087 2822303397761444553856631)
          ·
            refine ⟨4233455096642166830784947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2822303397761444553856631 4233455096642166830784947)
            ·
              refine ⟨6350182644963250246177421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4233455096642166830784947 6350182644963250246177421)
              ·
                refine ⟨2381318491861218842316533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6350182644963250246177421 2381318491861218842316533)
                ·
                  refine ⟨223248608611989266467175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2381318491861218842316533 223248608611989266467175)
                  ·
                    rfl

theorem cell21_978244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_978244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_978244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_978244 prefixEnd_978244 := by exact prefixLift 978244
  have htrace : WordTrace (prefixWord ++ tailWord_978244) baseStart_978244 baseEnd_978244 := by
    simpa [prefixWord, tailWord_978244, baseEnd_978244] using wordTrace_append hprefix tailTrace_978244
  have hstable : (prefixWord ++ tailWord_978244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978244).length < 2 ^ (prefixWord ++ tailWord_978244).sum := by decide
  have hdescent : baseEnd_978244 < baseStart_978244 := by decide
  rcases family_descends (prefixWord ++ tailWord_978244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978272 : List Nat := [2, 1, 1, 3, 4, 2, 1, 7]
def baseStart_978272 : Nat := 118140960795 + 978272 * 2 ^ 59
def prefixEnd_978272 : Nat := 4983230072969 + 3 ^ 40 * 978272 * 2
def baseEnd_978272 : Nat := 74418332864489146666817

theorem tailTrace_978272 : CollatzResearch.WordTrace tailWord_978272 prefixEnd_978272 74418332864489146666817 := by
  unfold tailWord_978272
  simp only [CollatzResearch.WordTrace]
  refine ⟨17840255555947547200572535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23787007407930062934096713 17840255555947547200572535)
  ·
    refine ⟨26760383333921320800858803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17840255555947547200572535 26760383333921320800858803)
    ·
      refine ⟨40140575000881981201288205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26760383333921320800858803 40140575000881981201288205)
      ·
        refine ⟨15052715625330742950483077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40140575000881981201288205 15052715625330742950483077)
        ·
          refine ⟨2822384179749514303215577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15052715625330742950483077 2822384179749514303215577)
          ·
            refine ⟨2116788134812135727411683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2822384179749514303215577 2116788134812135727411683)
            ·
              refine ⟨3175182202218203591117525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2116788134812135727411683 3175182202218203591117525)
              ·
                refine ⟨74418332864489146666817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3175182202218203591117525 74418332864489146666817)
                ·
                  rfl

theorem cell21_978272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 7].length) (baseStart_978272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_978272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_978272 prefixEnd_978272 := by exact prefixLift 978272
  have htrace : WordTrace (prefixWord ++ tailWord_978272) baseStart_978272 baseEnd_978272 := by
    simpa [prefixWord, tailWord_978272, baseEnd_978272] using wordTrace_append hprefix tailTrace_978272
  have hstable : (prefixWord ++ tailWord_978272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978272).length < 2 ^ (prefixWord ++ tailWord_978272).sum := by decide
  have hdescent : baseEnd_978272 < baseStart_978272 := by decide
  rcases family_descends (prefixWord ++ tailWord_978272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978306 : List Nat := [3, 4, 2, 1, 1, 2, 2, 6]
def baseStart_978306 : Nat := 118140960795 + 978306 * 2 ^ 59
def prefixEnd_978306 : Nat := 4983230072969 + 3 ^ 40 * 978306 * 2
def baseEnd_978306 : Nat := 74420919285563645477905

theorem tailTrace_978306 : CollatzResearch.WordTrace tailWord_978306 prefixEnd_978306 74420919285563645477905 := by
  unfold tailWord_978306
  simp only [CollatzResearch.WordTrace]
  refine ⟨8920437798442979551970693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23787834129181278805255181 8920437798442979551970693)
  ·
    refine ⟨1672582087208058665994505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8920437798442979551970693 1672582087208058665994505)
    ·
      refine ⟨1254436565406043999495879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1672582087208058665994505 1254436565406043999495879)
      ·
        refine ⟨1881654848109065999243819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1254436565406043999495879 1881654848109065999243819)
        ·
          refine ⟨2822482272163598998865729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1881654848109065999243819 2822482272163598998865729)
          ·
            refine ⟨2116861704122699249149297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2822482272163598998865729 2116861704122699249149297)
            ·
              refine ⟨1587646278092024436861973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2116861704122699249149297 1587646278092024436861973)
              ·
                refine ⟨74420919285563645477905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1587646278092024436861973 74420919285563645477905)
                ·
                  rfl

theorem cell21_978306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 6].length) (baseStart_978306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_978306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_978306 prefixEnd_978306 := by exact prefixLift 978306
  have htrace : WordTrace (prefixWord ++ tailWord_978306) baseStart_978306 baseEnd_978306 := by
    simpa [prefixWord, tailWord_978306, baseEnd_978306] using wordTrace_append hprefix tailTrace_978306
  have hstable : (prefixWord ++ tailWord_978306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978306).length < 2 ^ (prefixWord ++ tailWord_978306).sum := by decide
  have hdescent : baseEnd_978306 < baseStart_978306 := by decide
  rcases family_descends (prefixWord ++ tailWord_978306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978410 : List Nat := [3, 1, 3, 1, 4, 1, 1, 1, 6]
def baseStart_978410 : Nat := 118140960795 + 978410 * 2 ^ 59
def prefixEnd_978410 : Nat := 4983230072969 + 3 ^ 40 * 978410 * 2
def baseEnd_978410 : Nat := 223286492073609866700169

theorem tailTrace_978410 : CollatzResearch.WordTrace tailWord_978410 prefixEnd_978410 223286492073609866700169 := by
  unfold tailWord_978410
  simp only [CollatzResearch.WordTrace]
  refine ⟨8921386096348785992417171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23790362923596762646445789 8921386096348785992417171)
  ·
    refine ⟨13382079144523178988625757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8921386096348785992417171 13382079144523178988625757)
    ·
      refine ⟨5018279679196192120734659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13382079144523178988625757 5018279679196192120734659)
      ·
        refine ⟨7527419518794288181101989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5018279679196192120734659 7527419518794288181101989)
        ·
          refine ⟨1411391159773929033956623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7527419518794288181101989 1411391159773929033956623)
          ·
            refine ⟨2117086739660893550934935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1411391159773929033956623 2117086739660893550934935)
            ·
              refine ⟨3175630109491340326402403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2117086739660893550934935 3175630109491340326402403)
              ·
                refine ⟨4763445164237010489603605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3175630109491340326402403 4763445164237010489603605)
                ·
                  refine ⟨223286492073609866700169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4763445164237010489603605 223286492073609866700169)
                  ·
                    rfl

theorem cell21_978410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 6].length) (baseStart_978410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_978410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_978410 prefixEnd_978410 := by exact prefixLift 978410
  have htrace : WordTrace (prefixWord ++ tailWord_978410) baseStart_978410 baseEnd_978410 := by
    simpa [prefixWord, tailWord_978410, baseEnd_978410] using wordTrace_append hprefix tailTrace_978410
  have hstable : (prefixWord ++ tailWord_978410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978410).length < 2 ^ (prefixWord ++ tailWord_978410).sum := by decide
  have hdescent : baseEnd_978410 < baseStart_978410 := by decide
  rcases family_descends (prefixWord ++ tailWord_978410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978469 : List Nat := [1, 3, 1, 2, 2, 1, 1, 6, 4]
def baseStart_978469 : Nat := 118140960795 + 978469 * 2 ^ 59
def prefixEnd_978469 : Nat := 4983230072969 + 3 ^ 40 * 978469 * 2
def baseEnd_978469 : Nat := 223299956677438875216715

theorem tailTrace_978469 : CollatzResearch.WordTrace tailWord_978469 prefixEnd_978469 223299956677438875216715 := by
  unfold tailWord_978469
  simp only [CollatzResearch.WordTrace]
  refine ⟨35687696292181397046066461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23791797528120931364044307 35687696292181397046066461)
  ·
    refine ⟨13382886109568023892274923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35687696292181397046066461 13382886109568023892274923)
    ·
      refine ⟨20074329164352035838412385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13382886109568023892274923 20074329164352035838412385)
      ·
        refine ⟨15055746873264026878809289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20074329164352035838412385 15055746873264026878809289)
        ·
          refine ⟨11291810154948020159106967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15055746873264026878809289 11291810154948020159106967)
          ·
            refine ⟨16937715232422030238660451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11291810154948020159106967 16937715232422030238660451)
            ·
              refine ⟨25406572848633045357990677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16937715232422030238660451 25406572848633045357990677)
              ·
                refine ⟨1190933102279674001155813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25406572848633045357990677 1190933102279674001155813)
                ·
                  refine ⟨223299956677438875216715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1190933102279674001155813 223299956677438875216715)
                  ·
                    rfl

theorem cell21_978469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_978469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_978469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_978469 prefixEnd_978469 := by exact prefixLift 978469
  have htrace : WordTrace (prefixWord ++ tailWord_978469) baseStart_978469 baseEnd_978469 := by
    simpa [prefixWord, tailWord_978469, baseEnd_978469] using wordTrace_append hprefix tailTrace_978469
  have hstable : (prefixWord ++ tailWord_978469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978469).length < 2 ^ (prefixWord ++ tailWord_978469).sum := by decide
  have hdescent : baseEnd_978469 < baseStart_978469 := by decide
  rcases family_descends (prefixWord ++ tailWord_978469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978483 : List Nat := [1, 1, 1, 2, 4, 3, 1, 8]
def baseStart_978483 : Nat := 118140960795 + 978483 * 2 ^ 59
def prefixEnd_978483 : Nat := 4983230072969 + 3 ^ 40 * 978483 * 2
def baseEnd_978483 : Nat := 74434383889392653994451

theorem tailTrace_978483 : CollatzResearch.WordTrace tailWord_978483 prefixEnd_978483 74434383889392653994451 := by
  unfold tailWord_978483
  simp only [CollatzResearch.WordTrace]
  refine ⟨35688206914130677437076103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23792137942753784958050735 35688206914130677437076103)
  ·
    refine ⟨53532310371196016155614155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35688206914130677437076103 53532310371196016155614155)
    ·
      refine ⟨80298465556794024233421233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53532310371196016155614155 80298465556794024233421233)
      ·
        refine ⟨60223849167595518175065925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80298465556794024233421233 60223849167595518175065925)
        ·
          refine ⟨11291971718924159657824861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60223849167595518175065925 11291971718924159657824861)
          ·
            refine ⟨4234489394596559871684323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11291971718924159657824861 4234489394596559871684323)
            ·
              refine ⟨6351734091894839807526485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4234489394596559871684323 6351734091894839807526485)
              ·
                refine ⟨74434383889392653994451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6351734091894839807526485 74434383889392653994451)
                ·
                  rfl

theorem cell21_978483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 8].length) (baseStart_978483 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_978483 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_978483 prefixEnd_978483 := by exact prefixLift 978483
  have htrace : WordTrace (prefixWord ++ tailWord_978483) baseStart_978483 baseEnd_978483 := by
    simpa [prefixWord, tailWord_978483, baseEnd_978483] using wordTrace_append hprefix tailTrace_978483
  have hstable : (prefixWord ++ tailWord_978483).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978483).length < 2 ^ (prefixWord ++ tailWord_978483).sum := by decide
  have hdescent : baseEnd_978483 < baseStart_978483 := by decide
  rcases family_descends (prefixWord ++ tailWord_978483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978666 : List Nat := [3, 1, 3, 1, 1, 1, 2, 4, 5]
def baseStart_978666 : Nat := 118140960795 + 978666 * 2 ^ 59
def prefixEnd_978666 : Nat := 4983230072969 + 3 ^ 40 * 978666 * 2
def baseEnd_978666 : Nat := 223344914761410310432979

theorem tailTrace_978666 : CollatzResearch.WordTrace tailWord_978666 prefixEnd_978666 223344914761410310432979 := by
  unfold tailWord_978666
  simp only [CollatzResearch.WordTrace]
  refine ⟨8923720368116924922746963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23796587648311799793991901 8923720368116924922746963)
  ·
    refine ⟨13385580552175387384120445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8923720368116924922746963 13385580552175387384120445)
    ·
      refine ⟨5019592707065770269045167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13385580552175387384120445 5019592707065770269045167)
      ·
        refine ⟨7529389060598655403567751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5019592707065770269045167 7529389060598655403567751)
        ·
          refine ⟨11294083590897983105351627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7529389060598655403567751 11294083590897983105351627)
          ·
            refine ⟨16941125386346974658027441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11294083590897983105351627 16941125386346974658027441)
            ·
              refine ⟨12705844039760230993520581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16941125386346974658027441 12705844039760230993520581)
              ·
                refine ⟨2382345757455043311285109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12705844039760230993520581 2382345757455043311285109)
                ·
                  refine ⟨223344914761410310432979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2382345757455043311285109 223344914761410310432979)
                  ·
                    rfl

theorem cell21_978666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_978666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_978666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_978666 prefixEnd_978666 := by exact prefixLift 978666
  have htrace : WordTrace (prefixWord ++ tailWord_978666) baseStart_978666 baseEnd_978666 := by
    simpa [prefixWord, tailWord_978666, baseEnd_978666] using wordTrace_append hprefix tailTrace_978666
  have hstable : (prefixWord ++ tailWord_978666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978666).length < 2 ^ (prefixWord ++ tailWord_978666).sum := by decide
  have hdescent : baseEnd_978666 < baseStart_978666 := by decide
  rcases family_descends (prefixWord ++ tailWord_978666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978680 : List Nat := [2, 1, 2, 1, 1, 2, 2, 4, 6]
def baseStart_978680 : Nat := 118140960795 + 978680 * 2 ^ 59
def prefixEnd_978680 : Nat := 4983230072969 + 3 ^ 40 * 978680 * 2
def baseEnd_978680 : Nat := 223348109752149397199617

theorem tailTrace_978680 : CollatzResearch.WordTrace tailWord_978680 prefixEnd_978680 223348109752149397199617 := by
  unfold tailWord_978680
  simp only [CollatzResearch.WordTrace]
  refine ⟨17847696047208490040998747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23796928062944653387998329 17847696047208490040998747)
  ·
    refine ⟨26771544070812735061498121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17847696047208490040998747 26771544070812735061498121)
    ·
      refine ⟨20078658053109551296123591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26771544070812735061498121 20078658053109551296123591)
      ·
        refine ⟨30117987079664326944185387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20078658053109551296123591 30117987079664326944185387)
        ·
          refine ⟨45176980619496490416278081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30117987079664326944185387 45176980619496490416278081)
          ·
            refine ⟨33882735464622367812208561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45176980619496490416278081 33882735464622367812208561)
            ·
              refine ⟨25412051598466775859156421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33882735464622367812208561 25412051598466775859156421)
              ·
                refine ⟨4764759674712520473591829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25412051598466775859156421 4764759674712520473591829)
                ·
                  refine ⟨223348109752149397199617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4764759674712520473591829 223348109752149397199617)
                  ·
                    rfl

theorem cell21_978680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 6].length) (baseStart_978680 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_978680 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_978680 prefixEnd_978680 := by exact prefixLift 978680
  have htrace : WordTrace (prefixWord ++ tailWord_978680) baseStart_978680 baseEnd_978680 := by
    simpa [prefixWord, tailWord_978680, baseEnd_978680] using wordTrace_append hprefix tailTrace_978680
  have hstable : (prefixWord ++ tailWord_978680).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978680).length < 2 ^ (prefixWord ++ tailWord_978680).sum := by decide
  have hdescent : baseEnd_978680 < baseStart_978680 := by decide
  rcases family_descends (prefixWord ++ tailWord_978680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978700 : List Nat := [2, 2, 1, 2, 2, 1, 6, 2, 3]
def baseStart_978700 : Nat := 118140960795 + 978700 * 2 ^ 59
def prefixEnd_978700 : Nat := 4983230072969 + 3 ^ 40 * 978700 * 2
def baseEnd_978700 : Nat := 223352674024633806866243

theorem tailTrace_978700 : CollatzResearch.WordTrace tailWord_978700 prefixEnd_978700 223352674024633806866243 := by
  unfold tailWord_978700
  simp only [CollatzResearch.WordTrace]
  refine ⟨17848060777172261748862777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23797414369563015665150369 17848060777172261748862777)
  ·
    refine ⟨13386045582879196311647083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17848060777172261748862777 13386045582879196311647083)
    ·
      refine ⟨20079068374318794467470625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13386045582879196311647083 20079068374318794467470625)
      ·
        refine ⟨15059301280739095850602969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20079068374318794467470625 15059301280739095850602969)
        ·
          refine ⟨11294475960554321887952227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15059301280739095850602969 11294475960554321887952227)
          ·
            refine ⟨16941713940831482831928341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11294475960554321887952227 16941713940831482831928341)
            ·
              refine ⟨794142840976475757746641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16941713940831482831928341 794142840976475757746641)
              ·
                refine ⟨595607130732356818309981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 794142840976475757746641 595607130732356818309981)
                ·
                  refine ⟨223352674024633806866243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 595607130732356818309981 223352674024633806866243)
                  ·
                    rfl

theorem cell21_978700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 2, 3].length) (baseStart_978700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_978700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_978700 prefixEnd_978700 := by exact prefixLift 978700
  have htrace : WordTrace (prefixWord ++ tailWord_978700) baseStart_978700 baseEnd_978700 := by
    simpa [prefixWord, tailWord_978700, baseEnd_978700] using wordTrace_append hprefix tailTrace_978700
  have hstable : (prefixWord ++ tailWord_978700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978700).length < 2 ^ (prefixWord ++ tailWord_978700).sum := by decide
  have hdescent : baseEnd_978700 < baseStart_978700 := by decide
  rcases family_descends (prefixWord ++ tailWord_978700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978759 : List Nat := [1, 1, 4, 1, 2, 1, 4, 4, 3]
def baseStart_978759 : Nat := 118140960795 + 978759 * 2 ^ 59
def prefixEnd_978759 : Nat := 4983230072969 + 3 ^ 40 * 978759 * 2
def baseEnd_978759 : Nat := 223366138628462815382789

theorem tailTrace_978759 : CollatzResearch.WordTrace tailWord_978759 prefixEnd_978759 223366138628462815382789 := by
  unfold tailWord_978759
  simp only [CollatzResearch.WordTrace]
  refine ⟨35698273461130776574123331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23798848974087184382748887 35698273461130776574123331)
  ·
    refine ⟨53547410191696164861184997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35698273461130776574123331 53547410191696164861184997)
    ·
      refine ⟨10040139410943030911472187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53547410191696164861184997 10040139410943030911472187)
      ·
        refine ⟨15060209116414546367208281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10040139410943030911472187 15060209116414546367208281)
        ·
          refine ⟨11295156837310909775406211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15060209116414546367208281 11295156837310909775406211)
          ·
            refine ⟨16942735255966364663109317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11295156837310909775406211 16942735255966364663109317)
            ·
              refine ⟨3176762860493693374332997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16942735255966364663109317 3176762860493693374332997)
              ·
                refine ⟨595643036342567507687437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3176762860493693374332997 595643036342567507687437)
                ·
                  refine ⟨223366138628462815382789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 595643036342567507687437 223366138628462815382789)
                  ·
                    rfl

theorem cell21_978759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 4, 3].length) (baseStart_978759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_978759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_978759 prefixEnd_978759 := by exact prefixLift 978759
  have htrace : WordTrace (prefixWord ++ tailWord_978759) baseStart_978759 baseEnd_978759 := by
    simpa [prefixWord, tailWord_978759, baseEnd_978759] using wordTrace_append hprefix tailTrace_978759
  have hstable : (prefixWord ++ tailWord_978759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978759).length < 2 ^ (prefixWord ++ tailWord_978759).sum := by decide
  have hdescent : baseEnd_978759 < baseStart_978759 := by decide
  rcases family_descends (prefixWord ++ tailWord_978759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978824 : List Nat := [2, 1, 3, 3, 4, 1, 2, 1, 4]
def baseStart_978824 : Nat := 118140960795 + 978824 * 2 ^ 59
def prefixEnd_978824 : Nat := 4983230072969 + 3 ^ 40 * 978824 * 2
def baseEnd_978824 : Nat := 223380972514037146799323

theorem tailTrace_978824 : CollatzResearch.WordTrace tailWord_978824 prefixEnd_978824 223380972514037146799323 := by
  unfold tailWord_978824
  simp only [CollatzResearch.WordTrace]
  refine ⟨17850322102947646337619763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23800429470596861783493017 17850322102947646337619763)
  ·
    refine ⟨26775483154421469506429645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17850322102947646337619763 26775483154421469506429645)
    ·
      refine ⟨10040806182908051064911117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26775483154421469506429645 10040806182908051064911117)
      ·
        refine ⟨3765302318590519149341669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10040806182908051064911117 3765302318590519149341669)
        ·
          refine ⟨705994184735722340501563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3765302318590519149341669 705994184735722340501563)
          ·
            refine ⟨1058991277103583510752345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 705994184735722340501563 1058991277103583510752345)
            ·
              refine ⟨794243457827687633064259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1058991277103583510752345 794243457827687633064259)
              ·
                refine ⟨1191365186741531449596389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 794243457827687633064259 1191365186741531449596389)
                ·
                  refine ⟨223380972514037146799323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1191365186741531449596389 223380972514037146799323)
                  ·
                    rfl

theorem cell21_978824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 1, 4].length) (baseStart_978824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_978824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_978824 prefixEnd_978824 := by exact prefixLift 978824
  have htrace : WordTrace (prefixWord ++ tailWord_978824) baseStart_978824 baseEnd_978824 := by
    simpa [prefixWord, tailWord_978824, baseEnd_978824] using wordTrace_append hprefix tailTrace_978824
  have hstable : (prefixWord ++ tailWord_978824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978824).length < 2 ^ (prefixWord ++ tailWord_978824).sum := by decide
  have hdescent : baseEnd_978824 < baseStart_978824 := by decide
  rcases family_descends (prefixWord ++ tailWord_978824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978869 : List Nat := [1, 3, 3, 2, 1, 4, 2, 2, 3]
def baseStart_978869 : Nat := 118140960795 + 978869 * 2 ^ 59
def prefixEnd_978869 : Nat := 4983230072969 + 3 ^ 40 * 978869 * 2
def baseEnd_978869 : Nat := 223391242127127068549231

theorem tailTrace_978869 : CollatzResearch.WordTrace tailWord_978869 prefixEnd_978869 223391242127127068549231 := by
  unfold tailWord_978869
  simp only [CollatzResearch.WordTrace]
  refine ⟨35702285490732265360627661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23801523660488176907085107 35702285490732265360627661)
  ·
    refine ⟨13388357059024599510235373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35702285490732265360627661 13388357059024599510235373)
    ·
      refine ⟨5020633897134224816338265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13388357059024599510235373 5020633897134224816338265)
      ·
        refine ⟨3765475422850668612253699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5020633897134224816338265 3765475422850668612253699)
        ·
          refine ⟨5648213134276002918380549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3765475422850668612253699 5648213134276002918380549)
          ·
            refine ⟨1059039962676750547196353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5648213134276002918380549 1059039962676750547196353)
            ·
              refine ⟨794279972007562910397265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1059039962676750547196353 794279972007562910397265)
              ·
                refine ⟨595709979005672182797949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 794279972007562910397265 595709979005672182797949)
                ·
                  refine ⟨223391242127127068549231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 595709979005672182797949 223391242127127068549231)
                  ·
                    rfl

theorem cell21_978869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 2, 3].length) (baseStart_978869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_978869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_978869 prefixEnd_978869 := by exact prefixLift 978869
  have htrace : WordTrace (prefixWord ++ tailWord_978869) baseStart_978869 baseEnd_978869 := by
    simpa [prefixWord, tailWord_978869, baseEnd_978869] using wordTrace_append hprefix tailTrace_978869
  have hstable : (prefixWord ++ tailWord_978869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978869).length < 2 ^ (prefixWord ++ tailWord_978869).sum := by decide
  have hdescent : baseEnd_978869 < baseStart_978869 := by decide
  rcases family_descends (prefixWord ++ tailWord_978869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978894 : List Nat := [4, 1, 1, 1, 2, 2, 3, 2, 5]
def baseStart_978894 : Nat := 118140960795 + 978894 * 2 ^ 59
def prefixEnd_978894 : Nat := 4983230072969 + 3 ^ 40 * 978894 * 2
def baseEnd_978894 : Nat := 223396947467732580632513

theorem tailTrace_978894 : CollatzResearch.WordTrace tailWord_978894 prefixEnd_978894 223396947467732580632513 := by
  unfold tailWord_978894
  simp only [CollatzResearch.WordTrace]
  refine ⟨4462899664455211828785967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23802131543761129753525157 4462899664455211828785967)
  ·
    refine ⟨6694349496682817743178951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4462899664455211828785967 6694349496682817743178951)
    ·
      refine ⟨10041524245024226614768427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6694349496682817743178951 10041524245024226614768427)
      ·
        refine ⟨15062286367536339922152641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10041524245024226614768427 15062286367536339922152641)
        ·
          refine ⟨11296714775652254941614481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15062286367536339922152641 11296714775652254941614481)
          ·
            refine ⟨8472536081739191206210861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11296714775652254941614481 8472536081739191206210861)
            ·
              refine ⟨3177201030652196702329073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8472536081739191206210861 3177201030652196702329073)
              ·
                refine ⟨2382900772989147526746805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3177201030652196702329073 2382900772989147526746805)
                ·
                  refine ⟨223396947467732580632513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2382900772989147526746805 223396947467732580632513)
                  ·
                    rfl

theorem cell21_978894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_978894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_978894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_978894 prefixEnd_978894 := by exact prefixLift 978894
  have htrace : WordTrace (prefixWord ++ tailWord_978894) baseStart_978894 baseEnd_978894 := by
    simpa [prefixWord, tailWord_978894, baseEnd_978894] using wordTrace_append hprefix tailTrace_978894
  have hstable : (prefixWord ++ tailWord_978894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978894).length < 2 ^ (prefixWord ++ tailWord_978894).sum := by decide
  have hdescent : baseEnd_978894 < baseStart_978894 := by decide
  rcases family_descends (prefixWord ++ tailWord_978894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978911 : List Nat := [1, 1, 2, 3, 4, 1, 1, 5, 3]
def baseStart_978911 : Nat := 118140960795 + 978911 * 2 ^ 59
def prefixEnd_978911 : Nat := 4983230072969 + 3 ^ 40 * 978911 * 2
def baseEnd_978911 : Nat := 223400827099344328849145

theorem tailTrace_978911 : CollatzResearch.WordTrace tailWord_978911 prefixEnd_978911 223400827099344328849145 := by
  unfold tailWord_978911
  simp only [CollatzResearch.WordTrace]
  refine ⟨35703817356580106533656587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23802544904386737689104391 35703817356580106533656587)
  ·
    refine ⟨53555726034870159800484881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35703817356580106533656587 53555726034870159800484881)
    ·
      refine ⟨40166794526152619850363661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53555726034870159800484881 40166794526152619850363661)
      ·
        refine ⟨15062547947307232443886373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40166794526152619850363661 15062547947307232443886373)
        ·
          refine ⟨2824227740120106083228695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15062547947307232443886373 2824227740120106083228695)
          ·
            refine ⟨4236341610180159124843043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2824227740120106083228695 4236341610180159124843043)
            ·
              refine ⟨6354512415270238687264565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4236341610180159124843043 6354512415270238687264565)
              ·
                refine ⟨595735538931584876931053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6354512415270238687264565 595735538931584876931053)
                ·
                  refine ⟨223400827099344328849145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 595735538931584876931053 223400827099344328849145)
                  ·
                    rfl

theorem cell21_978911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 5, 3].length) (baseStart_978911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_978911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_978911 prefixEnd_978911 := by exact prefixLift 978911
  have htrace : WordTrace (prefixWord ++ tailWord_978911) baseStart_978911 baseEnd_978911 := by
    simpa [prefixWord, tailWord_978911, baseEnd_978911] using wordTrace_append hprefix tailTrace_978911
  have hstable : (prefixWord ++ tailWord_978911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978911).length < 2 ^ (prefixWord ++ tailWord_978911).sum := by decide
  have hdescent : baseEnd_978911 < baseStart_978911 := by decide
  rcases family_descends (prefixWord ++ tailWord_978911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979038 : List Nat := [4, 4, 1, 1, 2, 1, 1, 4, 3]
def baseStart_979038 : Nat := 118140960795 + 979038 * 2 ^ 59
def prefixEnd_979038 : Nat := 4983230072969 + 3 ^ 40 * 979038 * 2
def baseEnd_979038 : Nat := 223429810229620330232219

theorem tailTrace_979038 : CollatzResearch.WordTrace tailWord_979038 prefixEnd_979038 223429810229620330232219 := by
  unfold tailWord_979038
  simp only [CollatzResearch.WordTrace]
  refine ⟨4463556178390000902941221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23805632951413338149019845 4463556178390000902941221)
  ·
    refine ⟨836916783448125169301479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4463556178390000902941221 836916783448125169301479)
    ·
      refine ⟨1255375175172187753952219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 836916783448125169301479 1255375175172187753952219)
      ·
        refine ⟨1883062762758281630928329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1255375175172187753952219 1883062762758281630928329)
        ·
          refine ⟨1412297072068711223196247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1883062762758281630928329 1412297072068711223196247)
          ·
            refine ⟨2118445608103066834794371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1412297072068711223196247 2118445608103066834794371)
            ·
              refine ⟨3177668412154600252191557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2118445608103066834794371 3177668412154600252191557)
              ·
                refine ⟨595812827278987547285917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3177668412154600252191557 595812827278987547285917)
                ·
                  refine ⟨223429810229620330232219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 595812827278987547285917 223429810229620330232219)
                  ·
                    rfl

theorem cell21_979038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_979038 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_979038 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_979038 prefixEnd_979038 := by exact prefixLift 979038
  have htrace : WordTrace (prefixWord ++ tailWord_979038) baseStart_979038 baseEnd_979038 := by
    simpa [prefixWord, tailWord_979038, baseEnd_979038] using wordTrace_append hprefix tailTrace_979038
  have hstable : (prefixWord ++ tailWord_979038).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979038).length < 2 ^ (prefixWord ++ tailWord_979038).sum := by decide
  have hdescent : baseEnd_979038 < baseStart_979038 := by decide
  rcases family_descends (prefixWord ++ tailWord_979038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979080 : List Nat := [2, 1, 3, 4, 1, 2, 2, 3, 3]
def baseStart_979080 : Nat := 118140960795 + 979080 * 2 ^ 59
def prefixEnd_979080 : Nat := 4983230072969 + 3 ^ 40 * 979080 * 2
def baseEnd_979080 : Nat := 223439395201837590532133

theorem tailTrace_979080 : CollatzResearch.WordTrace tailWord_979080 prefixEnd_979080 223439395201837590532133 := by
  unfold tailWord_979080
  simp only [CollatzResearch.WordTrace]
  refine ⟨17854990646483924198279347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23806654195311898931039129 17854990646483924198279347)
  ·
    refine ⟨26782485969725886297419021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17854990646483924198279347 26782485969725886297419021)
    ·
      refine ⟨10043432238647207361532133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26782485969725886297419021 10043432238647207361532133)
      ·
        refine ⟨1883143544746351380287275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10043432238647207361532133 1883143544746351380287275)
        ·
          refine ⟨2824715317119527070430913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1883143544746351380287275 2824715317119527070430913)
          ·
            refine ⟨2118536487839645302823185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2824715317119527070430913 2118536487839645302823185)
            ·
              refine ⟨1588902365879733977117389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2118536487839645302823185 1588902365879733977117389)
              ·
                refine ⟨595838387204900241419021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1588902365879733977117389 595838387204900241419021)
                ·
                  refine ⟨223439395201837590532133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 595838387204900241419021 223439395201837590532133)
                  ·
                    rfl

theorem cell21_979080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 3, 3].length) (baseStart_979080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_979080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_979080 prefixEnd_979080 := by exact prefixLift 979080
  have htrace : WordTrace (prefixWord ++ tailWord_979080) baseStart_979080 baseEnd_979080 := by
    simpa [prefixWord, tailWord_979080, baseEnd_979080] using wordTrace_append hprefix tailTrace_979080
  have hstable : (prefixWord ++ tailWord_979080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979080).length < 2 ^ (prefixWord ++ tailWord_979080).sum := by decide
  have hdescent : baseEnd_979080 < baseStart_979080 := by decide
  rcases family_descends (prefixWord ++ tailWord_979080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979111 : List Nat := [1, 1, 6, 2, 2, 1, 3, 1, 4]
def baseStart_979111 : Nat := 118140960795 + 979111 * 2 ^ 59
def prefixEnd_979111 : Nat := 4983230072969 + 3 ^ 40 * 979111 * 2
def baseEnd_979111 : Nat := 223446469824188425515403

theorem tailTrace_979111 : CollatzResearch.WordTrace tailWord_979111 prefixEnd_979111 223446469824188425515403 := by
  unfold tailWord_979111
  simp only [CollatzResearch.WordTrace]
  refine ⟨35711111955855540690937187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23807407970570360460624791 35711111955855540690937187)
  ·
    refine ⟨53566667933783311036405781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35711111955855540690937187 53566667933783311036405781)
    ·
      refine ⟨2510937559396092704831521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 53566667933783311036405781 2510937559396092704831521)
      ·
        refine ⟨1883203169547069528623641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2510937559396092704831521 1883203169547069528623641)
        ·
          refine ⟨1412402377160302146467731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1883203169547069528623641 1412402377160302146467731)
          ·
            refine ⟨2118603565740453219701597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1412402377160302146467731 2118603565740453219701597)
            ·
              refine ⟨794476337152669957388099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2118603565740453219701597 794476337152669957388099)
              ·
                refine ⟨1191714505729004936082149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 794476337152669957388099 1191714505729004936082149)
                ·
                  refine ⟨223446469824188425515403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1191714505729004936082149 223446469824188425515403)
                  ·
                    rfl

theorem cell21_979111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 1, 4].length) (baseStart_979111 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_979111 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_979111 prefixEnd_979111 := by exact prefixLift 979111
  have htrace : WordTrace (prefixWord ++ tailWord_979111) baseStart_979111 baseEnd_979111 := by
    simpa [prefixWord, tailWord_979111, baseEnd_979111] using wordTrace_append hprefix tailTrace_979111
  have hstable : (prefixWord ++ tailWord_979111).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979111).length < 2 ^ (prefixWord ++ tailWord_979111).sum := by decide
  have hdescent : baseEnd_979111 < baseStart_979111 := by decide
  rcases family_descends (prefixWord ++ tailWord_979111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979136 : List Nat := [2, 1, 1, 2, 5, 1, 1, 2, 6]
def baseStart_979136 : Nat := 118140960795 + 979136 * 2 ^ 59
def prefixEnd_979136 : Nat := 4983230072969 + 3 ^ 40 * 979136 * 2
def baseEnd_979136 : Nat := 223452175164793937598685

theorem tailTrace_979136 : CollatzResearch.WordTrace tailWord_979136 prefixEnd_979136 223452175164793937598685 := by
  unfold tailWord_979136
  simp only [CollatzResearch.WordTrace]
  refine ⟨17856011890382484980298631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23808015853843313307064841 17856011890382484980298631)
  ·
    refine ⟨26784017835573727470447947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17856011890382484980298631 26784017835573727470447947)
    ·
      refine ⟨40176026753360591205671921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26784017835573727470447947 40176026753360591205671921)
      ·
        refine ⟨30132020065020443404253941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40176026753360591205671921 30132020065020443404253941)
        ·
          refine ⟨2824876881095666569148807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30132020065020443404253941 2824876881095666569148807)
          ·
            refine ⟨4237315321643499853723211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2824876881095666569148807 4237315321643499853723211)
            ·
              refine ⟨6355972982465249780584817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4237315321643499853723211 6355972982465249780584817)
              ·
                refine ⟨4766979736848937335438613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6355972982465249780584817 4766979736848937335438613)
                ·
                  refine ⟨223452175164793937598685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4766979736848937335438613 223452175164793937598685)
                  ·
                    rfl

theorem cell21_979136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 6].length) (baseStart_979136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_979136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_979136 prefixEnd_979136 := by exact prefixLift 979136
  have htrace : WordTrace (prefixWord ++ tailWord_979136) baseStart_979136 baseEnd_979136 := by
    simpa [prefixWord, tailWord_979136, baseEnd_979136] using wordTrace_append hprefix tailTrace_979136
  have hstable : (prefixWord ++ tailWord_979136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979136).length < 2 ^ (prefixWord ++ tailWord_979136).sum := by decide
  have hdescent : baseEnd_979136 < baseStart_979136 := by decide
  rcases family_descends (prefixWord ++ tailWord_979136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979308 : List Nat := [2, 2, 1, 1, 6, 2, 1, 3, 3]
def baseStart_979308 : Nat := 118140960795 + 979308 * 2 ^ 59
def prefixEnd_979308 : Nat := 4983230072969 + 3 ^ 40 * 979308 * 2
def baseEnd_979308 : Nat := 223491427908159860731667

theorem tailTrace_979308 : CollatzResearch.WordTrace tailWord_979308 prefixEnd_979308 223491427908159860731667 := by
  unfold tailWord_979308
  simp only [CollatzResearch.WordTrace]
  refine ⟨17859148568070921667929289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23812198090761228890572385 17859148568070921667929289)
  ·
    refine ⟨13394361426053191250946967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17859148568070921667929289 13394361426053191250946967)
    ·
      refine ⟨20091542139079786876420451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13394361426053191250946967 20091542139079786876420451)
      ·
        refine ⟨30137313208619680314630677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20091542139079786876420451 30137313208619680314630677)
        ·
          refine ⟨1412686556654047514748313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30137313208619680314630677 1412686556654047514748313)
          ·
            refine ⟨1059514917490535636061235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1412686556654047514748313 1059514917490535636061235)
            ·
              refine ⟨1589272376235803454091853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1059514917490535636061235 1589272376235803454091853)
              ·
                refine ⟨595977141088426295284445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1589272376235803454091853 595977141088426295284445)
                ·
                  refine ⟨223491427908159860731667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 595977141088426295284445 223491427908159860731667)
                  ·
                    rfl

theorem cell21_979308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 3, 3].length) (baseStart_979308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_979308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_979308 prefixEnd_979308 := by exact prefixLift 979308
  have htrace : WordTrace (prefixWord ++ tailWord_979308) baseStart_979308 baseEnd_979308 := by
    simpa [prefixWord, tailWord_979308, baseEnd_979308] using wordTrace_append hprefix tailTrace_979308
  have hstable : (prefixWord ++ tailWord_979308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979308).length < 2 ^ (prefixWord ++ tailWord_979308).sum := by decide
  have hdescent : baseEnd_979308 < baseStart_979308 := by decide
  rcases family_descends (prefixWord ++ tailWord_979308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979412 : List Nat := [2, 4, 1, 2, 2, 2, 3, 5]
def baseStart_979412 : Nat := 118140960795 + 979412 * 2 ^ 59
def prefixEnd_979412 : Nat := 4983230072969 + 3 ^ 40 * 979412 * 2
def baseEnd_979412 : Nat := 74505054041692930332707

theorem tailTrace_979412 : CollatzResearch.WordTrace tailWord_979412 prefixEnd_979412 74505054041692930332707 := by
  unfold tailWord_979412
  simp only [CollatzResearch.WordTrace]
  refine ⟨17861045163882534548822245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23814726885176712731762993 17861045163882534548822245)
  ·
    refine ⟨3348945968227975227904171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17861045163882534548822245 3348945968227975227904171)
    ·
      refine ⟨5023418952341962841856257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3348945968227975227904171 5023418952341962841856257)
      ·
        refine ⟨3767564214256472131392193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5023418952341962841856257 3767564214256472131392193)
        ·
          refine ⟨2825673160692354098544145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3767564214256472131392193 2825673160692354098544145)
          ·
            refine ⟨2119254870519265573908109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2825673160692354098544145 2119254870519265573908109)
            ·
              refine ⟨794720576444724590215541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2119254870519265573908109 794720576444724590215541)
              ·
                refine ⟨74505054041692930332707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 794720576444724590215541 74505054041692930332707)
                ·
                  rfl

theorem cell21_979412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 5].length) (baseStart_979412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_979412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_979412 prefixEnd_979412 := by exact prefixLift 979412
  have htrace : WordTrace (prefixWord ++ tailWord_979412) baseStart_979412 baseEnd_979412 := by
    simpa [prefixWord, tailWord_979412, baseEnd_979412] using wordTrace_append hprefix tailTrace_979412
  have hstable : (prefixWord ++ tailWord_979412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979412).length < 2 ^ (prefixWord ++ tailWord_979412).sum := by decide
  have hdescent : baseEnd_979412 < baseStart_979412 := by decide
  rcases family_descends (prefixWord ++ tailWord_979412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979488 : List Nat := [2, 1, 1, 6, 3, 1, 7]
def baseStart_979488 : Nat := 118140960795 + 979488 * 2 ^ 59
def prefixEnd_979488 : Nat := 4983230072969 + 3 ^ 40 * 979488 * 2
def baseEnd_979488 : Nat := 24836945151168838636811

theorem tailTrace_979488 : CollatzResearch.WordTrace tailWord_979488 prefixEnd_979488 24836945151168838636811 := by
  unfold tailWord_979488
  simp only [CollatzResearch.WordTrace]
  refine ⟨17862431137744867038705559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23816574850326489384940745 17862431137744867038705559)
  ·
    refine ⟨26793646706617300558058339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17862431137744867038705559 26793646706617300558058339)
    ·
      refine ⟨40190470059925950837087509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26793646706617300558058339 40190470059925950837087509)
      ·
        refine ⟨1883928284059028945488477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 40190470059925950837087509 1883928284059028945488477)
        ·
          refine ⟨706473106522135854558179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1883928284059028945488477 706473106522135854558179)
          ·
            refine ⟨1059709659783203781837269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706473106522135854558179 1059709659783203781837269)
            ·
              refine ⟨24836945151168838636811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1059709659783203781837269 24836945151168838636811)
              ·
                rfl

theorem cell21_979488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 7].length) (baseStart_979488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_979488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_979488 prefixEnd_979488 := by exact prefixLift 979488
  have htrace : WordTrace (prefixWord ++ tailWord_979488) baseStart_979488 baseEnd_979488 := by
    simpa [prefixWord, tailWord_979488, baseEnd_979488] using wordTrace_append hprefix tailTrace_979488
  have hstable : (prefixWord ++ tailWord_979488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979488).length < 2 ^ (prefixWord ++ tailWord_979488).sum := by decide
  have hdescent : baseEnd_979488 < baseStart_979488 := by decide
  rcases family_descends (prefixWord ++ tailWord_979488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979508 : List Nat := [2, 5, 1, 3, 1, 2, 2, 1, 4]
def baseStart_979508 : Nat := 118140960795 + 979508 * 2 ^ 59
def prefixEnd_979508 : Nat := 4983230072969 + 3 ^ 40 * 979508 * 2
def baseEnd_979508 : Nat := 223537070633003957397925

theorem tailTrace_979508 : CollatzResearch.WordTrace tailWord_979508 prefixEnd_979508 223537070633003957397925 := by
  unfold tailWord_979508
  simp only [CollatzResearch.WordTrace]
  refine ⟨17862795867708638746569589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23817061156944851662092785 17862795867708638746569589)
  ·
    refine ⟨1674637112597684882490899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17862795867708638746569589 1674637112597684882490899)
    ·
      refine ⟨2511955668896527323736349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1674637112597684882490899 2511955668896527323736349)
      ·
        refine ⟨941983375836197746401131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2511955668896527323736349 941983375836197746401131)
        ·
          refine ⟨1412975063754296619601697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 941983375836197746401131 1412975063754296619601697)
          ·
            refine ⟨1059731297815722464701273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1412975063754296619601697 1059731297815722464701273)
            ·
              refine ⟨794798473361791848525955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1059731297815722464701273 794798473361791848525955)
              ·
                refine ⟨1192197710042687772788933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 794798473361791848525955 1192197710042687772788933)
                ·
                  refine ⟨223537070633003957397925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1192197710042687772788933 223537070633003957397925)
                  ·
                    rfl

theorem cell21_979508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_979508 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_979508 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_979508 prefixEnd_979508 := by exact prefixLift 979508
  have htrace : WordTrace (prefixWord ++ tailWord_979508) baseStart_979508 baseEnd_979508 := by
    simpa [prefixWord, tailWord_979508, baseEnd_979508] using wordTrace_append hprefix tailTrace_979508
  have hstable : (prefixWord ++ tailWord_979508).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979508).length < 2 ^ (prefixWord ++ tailWord_979508).sum := by decide
  have hdescent : baseEnd_979508 < baseStart_979508 := by decide
  rcases family_descends (prefixWord ++ tailWord_979508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979530 : List Nat := [3, 1, 2, 1, 1, 4, 2, 7]
def baseStart_979530 : Nat := 118140960795 + 979530 * 2 ^ 59
def prefixEnd_979530 : Nat := 4983230072969 + 3 ^ 40 * 979530 * 2
def baseEnd_979530 : Nat := 74514030444245602677071

theorem tailTrace_979530 : CollatzResearch.WordTrace tailWord_979530 prefixEnd_979530 74514030444245602677071 := by
  unfold tailWord_979530
  simp only [CollatzResearch.WordTrace]
  refine ⟨8931598535334393812610011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23817596094225050166960029 8931598535334393812610011)
  ·
    refine ⟨13397397803001590718915017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8931598535334393812610011 13397397803001590718915017)
    ·
      refine ⟨10048048352251193039186263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13397397803001590718915017 10048048352251193039186263)
      ·
        refine ⟨15072072528376789558779395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10048048352251193039186263 15072072528376789558779395)
        ·
          refine ⟨22608108792565184338169093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15072072528376789558779395 22608108792565184338169093)
          ·
            refine ⟨4239020398605972063406705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22608108792565184338169093 4239020398605972063406705)
            ·
              refine ⟨3179265298954479047555029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4239020398605972063406705 3179265298954479047555029)
              ·
                refine ⟨74514030444245602677071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3179265298954479047555029 74514030444245602677071)
                ·
                  rfl

theorem cell21_979530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 7].length) (baseStart_979530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_979530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_979530 prefixEnd_979530 := by exact prefixLift 979530
  have htrace : WordTrace (prefixWord ++ tailWord_979530) baseStart_979530 baseEnd_979530 := by
    simpa [prefixWord, tailWord_979530, baseEnd_979530] using wordTrace_append hprefix tailTrace_979530
  have hstable : (prefixWord ++ tailWord_979530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979530).length < 2 ^ (prefixWord ++ tailWord_979530).sum := by decide
  have hdescent : baseEnd_979530 < baseStart_979530 := by decide
  rcases family_descends (prefixWord ++ tailWord_979530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979671 : List Nat := [1, 1, 3, 2, 1, 5, 3, 2, 3]
def baseStart_979671 : Nat := 118140960795 + 979671 * 2 ^ 59
def prefixEnd_979671 : Nat := 4983230072969 + 3 ^ 40 * 979671 * 2
def baseEnd_979671 : Nat := 223574269453751896180925

theorem tailTrace_979671 : CollatzResearch.WordTrace tailWord_979671 prefixEnd_979671 223574269453751896180925 := by
  unfold tailWord_979671
  simp only [CollatzResearch.WordTrace]
  refine ⟨35731536833826756331322867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23821024555884504220881911 35731536833826756331322867)
  ·
    refine ⟨53597305250740134496984301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35731536833826756331322867 53597305250740134496984301)
    ·
      refine ⟨20098989469027550436369113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53597305250740134496984301 20098989469027550436369113)
      ·
        refine ⟨15074242101770662827276835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20098989469027550436369113 15074242101770662827276835)
        ·
          refine ⟨22611363152655994240915253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15074242101770662827276835 22611363152655994240915253)
          ·
            refine ⟨2119815295561499460085805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22611363152655994240915253 2119815295561499460085805)
            ·
              refine ⟨794930735835562297532177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2119815295561499460085805 794930735835562297532177)
              ·
                refine ⟨596198051876671723149133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 794930735835562297532177 596198051876671723149133)
                ·
                  refine ⟨223574269453751896180925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 596198051876671723149133 223574269453751896180925)
                  ·
                    rfl

theorem cell21_979671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 2, 3].length) (baseStart_979671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_979671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_979671 prefixEnd_979671 := by exact prefixLift 979671
  have htrace : WordTrace (prefixWord ++ tailWord_979671) baseStart_979671 baseEnd_979671 := by
    simpa [prefixWord, tailWord_979671, baseEnd_979671] using wordTrace_append hprefix tailTrace_979671
  have hstable : (prefixWord ++ tailWord_979671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979671).length < 2 ^ (prefixWord ++ tailWord_979671).sum := by decide
  have hdescent : baseEnd_979671 < baseStart_979671 := by decide
  rcases family_descends (prefixWord ++ tailWord_979671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979685 : List Nat := [1, 3, 1, 4, 1, 2, 4, 1, 4]
def baseStart_979685 : Nat := 118140960795 + 979685 * 2 ^ 59
def prefixEnd_979685 : Nat := 4983230072969 + 3 ^ 40 * 979685 * 2
def baseEnd_979685 : Nat := 223577464444490982947563

theorem tailTrace_979685 : CollatzResearch.WordTrace tailWord_979685 prefixEnd_979685 223577464444490982947563 := by
  unfold tailWord_979685
  simp only [CollatzResearch.WordTrace]
  refine ⟨35732047455776036722332509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23821364970517357814888339 35732047455776036722332509)
  ·
    refine ⟨13399517795916013770874691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35732047455776036722332509 13399517795916013770874691)
    ·
      refine ⟨20099276693874020656312037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13399517795916013770874691 20099276693874020656312037)
      ·
        refine ⟨3768614380101378873058507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20099276693874020656312037 3768614380101378873058507)
        ·
          refine ⟨5652921570152068309587761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3768614380101378873058507 5652921570152068309587761)
          ·
            refine ⟨4239691177614051232190821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5652921570152068309587761 4239691177614051232190821)
            ·
              refine ⟨794942095802634606035779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4239691177614051232190821 794942095802634606035779)
              ·
                refine ⟨1192413143703951909053669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 794942095802634606035779 1192413143703951909053669)
                ·
                  refine ⟨223577464444490982947563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1192413143703951909053669 223577464444490982947563)
                  ·
                    rfl

theorem cell21_979685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 1, 4].length) (baseStart_979685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_979685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_979685 prefixEnd_979685 := by exact prefixLift 979685
  have htrace : WordTrace (prefixWord ++ tailWord_979685) baseStart_979685 baseEnd_979685 := by
    simpa [prefixWord, tailWord_979685, baseEnd_979685] using wordTrace_append hprefix tailTrace_979685
  have hstable : (prefixWord ++ tailWord_979685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979685).length < 2 ^ (prefixWord ++ tailWord_979685).sum := by decide
  have hdescent : baseEnd_979685 < baseStart_979685 := by decide
  rcases family_descends (prefixWord ++ tailWord_979685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979696 : List Nat := [2, 1, 1, 1, 3, 1, 4, 1, 7]
def baseStart_979696 : Nat := 118140960795 + 979696 * 2 ^ 59
def prefixEnd_979696 : Nat := 4983230072969 + 3 ^ 40 * 979696 * 2
def baseEnd_979696 : Nat := 223579974794357408264207

theorem tailTrace_979696 : CollatzResearch.WordTrace tailWord_979696 prefixEnd_979696 223579974794357408264207 := by
  unfold tailWord_979696
  simp only [CollatzResearch.WordTrace]
  refine ⟨17866224329368092800491471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23821632439157457067321961 17866224329368092800491471)
  ·
    refine ⟨26799336494052139200737207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17866224329368092800491471 26799336494052139200737207)
    ·
      refine ⟨40199004741078208801105811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26799336494052139200737207 40199004741078208801105811)
      ·
        refine ⟨60298507111617313201658717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40199004741078208801105811 60298507111617313201658717)
        ·
          refine ⟨22611940166856492450622019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60298507111617313201658717 22611940166856492450622019)
          ·
            refine ⟨33917910250284738675933029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22611940166856492450622019 33917910250284738675933029)
            ·
              refine ⟨6359608171928388501737443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33917910250284738675933029 6359608171928388501737443)
              ·
                refine ⟨9539412257892582752606165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6359608171928388501737443 9539412257892582752606165)
                ·
                  refine ⟨223579974794357408264207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9539412257892582752606165 223579974794357408264207)
                  ·
                    rfl

theorem cell21_979696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 7].length) (baseStart_979696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_979696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_979696 prefixEnd_979696 := by exact prefixLift 979696
  have htrace : WordTrace (prefixWord ++ tailWord_979696) baseStart_979696 baseEnd_979696 := by
    simpa [prefixWord, tailWord_979696, baseEnd_979696] using wordTrace_append hprefix tailTrace_979696
  have hstable : (prefixWord ++ tailWord_979696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979696).length < 2 ^ (prefixWord ++ tailWord_979696).sum := by decide
  have hdescent : baseEnd_979696 < baseStart_979696 := by decide
  rcases family_descends (prefixWord ++ tailWord_979696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979744 : List Nat := [2, 1, 1, 5, 1, 2, 2, 3, 4]
def baseStart_979744 : Nat := 118140960795 + 979744 * 2 ^ 59
def prefixEnd_979744 : Nat := 4983230072969 + 3 ^ 40 * 979744 * 2
def baseEnd_979744 : Nat := 223590929048319991464109

theorem tailTrace_979744 : CollatzResearch.WordTrace tailWord_979744 prefixEnd_979744 223590929048319991464109 := by
  unfold tailWord_979744
  simp only [CollatzResearch.WordTrace]
  refine ⟨17867099681281144899365143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23822799575041526532486857 17867099681281144899365143)
  ·
    refine ⟨26800649521921717349047715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17867099681281144899365143 26800649521921717349047715)
    ·
      refine ⟨40200974282882576023571573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26800649521921717349047715 40200974282882576023571573)
      ·
        refine ⟨3768841339020241502209835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40200974282882576023571573 3768841339020241502209835)
        ·
          refine ⟨5653262008530362253314753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3768841339020241502209835 5653262008530362253314753)
          ·
            refine ⟨4239946506397771689986065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5653262008530362253314753 4239946506397771689986065)
            ·
              refine ⟨3179959879798328767489549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4239946506397771689986065 3179959879798328767489549)
              ·
                refine ⟨1192484954924373287808581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3179959879798328767489549 1192484954924373287808581)
                ·
                  refine ⟨223590929048319991464109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1192484954924373287808581 223590929048319991464109)
                  ·
                    rfl

theorem cell21_979744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3, 4].length) (baseStart_979744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_979744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_979744 prefixEnd_979744 := by exact prefixLift 979744
  have htrace : WordTrace (prefixWord ++ tailWord_979744) baseStart_979744 baseEnd_979744 := by
    simpa [prefixWord, tailWord_979744, baseEnd_979744] using wordTrace_append hprefix tailTrace_979744
  have hstable : (prefixWord ++ tailWord_979744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979744).length < 2 ^ (prefixWord ++ tailWord_979744).sum := by decide
  have hdescent : baseEnd_979744 < baseStart_979744 := by decide
  rcases family_descends (prefixWord ++ tailWord_979744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979764 : List Nat := [2, 5, 1, 1, 3, 1, 2, 3, 3]
def baseStart_979764 : Nat := 118140960795 + 979764 * 2 ^ 59
def prefixEnd_979764 : Nat := 4983230072969 + 3 ^ 40 * 979764 * 2
def baseEnd_979764 : Nat := 223595493320804401130735

theorem tailTrace_979764 : CollatzResearch.WordTrace tailWord_979764 prefixEnd_979764 223595493320804401130735 := by
  unfold tailWord_979764
  simp only [CollatzResearch.WordTrace]
  refine ⟨17867464411244916607229173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23823285881659888809638897 17867464411244916607229173)
  ·
    refine ⟨1675074788554210931927735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17867464411244916607229173 1675074788554210931927735)
    ·
      refine ⟨2512612182831316397891603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1675074788554210931927735 2512612182831316397891603)
      ·
        refine ⟨3768918274246974596837405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2512612182831316397891603 3768918274246974596837405)
        ·
          refine ⟨1413344352842615473814027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3768918274246974596837405 1413344352842615473814027)
          ·
            refine ⟨2120016529263923210721041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1413344352842615473814027 2120016529263923210721041)
            ·
              refine ⟨1590012396947942408040781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2120016529263923210721041 1590012396947942408040781)
              ·
                refine ⟨596254648855478403015293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1590012396947942408040781 596254648855478403015293)
                ·
                  refine ⟨223595493320804401130735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 596254648855478403015293 223595493320804401130735)
                  ·
                    rfl

theorem cell21_979764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_979764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_979764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_979764 prefixEnd_979764 := by exact prefixLift 979764
  have htrace : WordTrace (prefixWord ++ tailWord_979764) baseStart_979764 baseEnd_979764 := by
    simpa [prefixWord, tailWord_979764, baseEnd_979764] using wordTrace_append hprefix tailTrace_979764
  have hstable : (prefixWord ++ tailWord_979764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979764).length < 2 ^ (prefixWord ++ tailWord_979764).sum := by decide
  have hdescent : baseEnd_979764 < baseStart_979764 := by decide
  rcases family_descends (prefixWord ++ tailWord_979764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979772 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 9]
def baseStart_979772 : Nat := 118140960795 + 979772 * 2 ^ 59
def prefixEnd_979772 : Nat := 4983230072969 + 3 ^ 40 * 979772 * 2
def baseEnd_979772 : Nat := 223597319029798164997385

theorem tailTrace_979772 : CollatzResearch.WordTrace tailWord_979772 prefixEnd_979772 223597319029798164997385 := by
  unfold tailWord_979772
  simp only [CollatzResearch.WordTrace]
  refine ⟨17867610303230425290374785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23823480404307233720499713 17867610303230425290374785)
  ·
    refine ⟨13400707727422818967781089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17867610303230425290374785 13400707727422818967781089)
    ·
      refine ⟨10050530795567114225835817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13400707727422818967781089 10050530795567114225835817)
      ·
        refine ⟨7537898096675335669376863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10050530795567114225835817 7537898096675335669376863)
        ·
          refine ⟨11306847145013003504065295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7537898096675335669376863 11306847145013003504065295)
          ·
            refine ⟨16960270717519505256097943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11306847145013003504065295 16960270717519505256097943)
            ·
              refine ⟨25440406076279257884146915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16960270717519505256097943 25440406076279257884146915)
              ·
                refine ⟨38160609114418886826220373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25440406076279257884146915 38160609114418886826220373)
                ·
                  refine ⟨223597319029798164997385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 38160609114418886826220373 223597319029798164997385)
                  ·
                    rfl

theorem cell21_979772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_979772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_979772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_979772 prefixEnd_979772 := by exact prefixLift 979772
  have htrace : WordTrace (prefixWord ++ tailWord_979772) baseStart_979772 baseEnd_979772 := by
    simpa [prefixWord, tailWord_979772, baseEnd_979772] using wordTrace_append hprefix tailTrace_979772
  have hstable : (prefixWord ++ tailWord_979772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979772).length < 2 ^ (prefixWord ++ tailWord_979772).sum := by decide
  have hdescent : baseEnd_979772 < baseStart_979772 := by decide
  rcases family_descends (prefixWord ++ tailWord_979772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979896 : List Nat := [2, 1, 2, 1, 2, 5, 2, 2, 4]
def baseStart_979896 : Nat := 118140960795 + 979896 * 2 ^ 59
def prefixEnd_979896 : Nat := 4983230072969 + 3 ^ 40 * 979896 * 2
def baseEnd_979896 : Nat := 223625617519201504930465

theorem tailTrace_979896 : CollatzResearch.WordTrace tailWord_979896 prefixEnd_979896 223625617519201504930465 := by
  unfold tailWord_979896
  simp only [CollatzResearch.WordTrace]
  refine ⟨17869871629005809879131771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23826495505341079838842361 17869871629005809879131771)
  ·
    refine ⟨26804807443508714818697657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17869871629005809879131771 26804807443508714818697657)
    ·
      refine ⟨20103605582631536114023243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26804807443508714818697657 20103605582631536114023243)
      ·
        refine ⟨30155408373947304171034865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20103605582631536114023243 30155408373947304171034865)
        ·
          refine ⟨22616556280460478128276149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30155408373947304171034865 22616556280460478128276149)
          ·
            refine ⟨2120302151293169824525889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22616556280460478128276149 2120302151293169824525889)
            ·
              refine ⟨1590226613469877368394417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2120302151293169824525889 1590226613469877368394417)
              ·
                refine ⟨1192669960102408026295813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1590226613469877368394417 1192669960102408026295813)
                ·
                  refine ⟨223625617519201504930465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1192669960102408026295813 223625617519201504930465)
                  ·
                    rfl

theorem cell21_979896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2, 4].length) (baseStart_979896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_979896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_979896 prefixEnd_979896 := by exact prefixLift 979896
  have htrace : WordTrace (prefixWord ++ tailWord_979896) baseStart_979896 baseEnd_979896 := by
    simpa [prefixWord, tailWord_979896, baseEnd_979896] using wordTrace_append hprefix tailTrace_979896
  have hstable : (prefixWord ++ tailWord_979896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979896).length < 2 ^ (prefixWord ++ tailWord_979896).sum := by decide
  have hdescent : baseEnd_979896 < baseStart_979896 := by decide
  rcases family_descends (prefixWord ++ tailWord_979896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979958 : List Nat := [5, 1, 1, 1, 3, 2, 2, 1, 5]
def baseStart_979958 : Nat := 118140960795 + 979958 * 2 ^ 59
def prefixEnd_979958 : Nat := 4983230072969 + 3 ^ 40 * 979958 * 2
def baseEnd_979958 : Nat := 223639766763903174897005

theorem tailTrace_979958 : CollatzResearch.WordTrace tailWord_979958 prefixEnd_979958 223639766763903174897005 := by
  unfold tailWord_979958
  simp only [CollatzResearch.WordTrace]
  refine ⟨2233875286486687771688783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23828003055858002898013685 2233875286486687771688783)
  ·
    refine ⟨3350812929730031657533175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2233875286486687771688783 3350812929730031657533175)
    ·
      refine ⟨5026219394595047486299763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3350812929730031657533175 5026219394595047486299763)
      ·
        refine ⟨7539329091892571229449645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5026219394595047486299763 7539329091892571229449645)
        ·
          refine ⟨2827248409459714211043617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7539329091892571229449645 2827248409459714211043617)
          ·
            refine ⟨2120436307094785658282713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2827248409459714211043617 2120436307094785658282713)
            ·
              refine ⟨1590327230321089243712035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2120436307094785658282713 1590327230321089243712035)
              ·
                refine ⟨2385490845481633865568053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1590327230321089243712035 2385490845481633865568053)
                ·
                  refine ⟨223639766763903174897005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2385490845481633865568053 223639766763903174897005)
                  ·
                    rfl

theorem cell21_979958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_979958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_979958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_979958 prefixEnd_979958 := by exact prefixLift 979958
  have htrace : WordTrace (prefixWord ++ tailWord_979958) baseStart_979958 baseEnd_979958 := by
    simpa [prefixWord, tailWord_979958, baseEnd_979958] using wordTrace_append hprefix tailTrace_979958
  have hstable : (prefixWord ++ tailWord_979958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979958).length < 2 ^ (prefixWord ++ tailWord_979958).sum := by decide
  have hdescent : baseEnd_979958 < baseStart_979958 := by decide
  rcases family_descends (prefixWord ++ tailWord_979958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980076 : List Nat := [2, 2, 1, 1, 3, 2, 2, 3, 5]
def baseStart_980076 : Nat := 118140960795 + 980076 * 2 ^ 59
def prefixEnd_980076 : Nat := 4983230072969 + 3 ^ 40 * 980076 * 2
def baseEnd_980076 : Nat := 223666695971561191930097

theorem tailTrace_980076 : CollatzResearch.WordTrace tailWord_980076 prefixEnd_980076 223666695971561191930097 := by
  unfold tailWord_980076
  simp only [CollatzResearch.WordTrace]
  refine ⟨17873154198679755249908041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23830872264906340333210721 17873154198679755249908041)
  ·
    refine ⟨13404865649009816437431031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17873154198679755249908041 13404865649009816437431031)
    ·
      refine ⟨20107298473514724656146547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13404865649009816437431031 20107298473514724656146547)
      ·
        refine ⟨30160947710272086984219821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20107298473514724656146547 30160947710272086984219821)
        ·
          refine ⟨11310355391352032619082433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30160947710272086984219821 11310355391352032619082433)
          ·
            refine ⟨8482766543514024464311825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11310355391352032619082433 8482766543514024464311825)
            ·
              refine ⟨6362074907635518348233869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8482766543514024464311825 6362074907635518348233869)
              ·
                refine ⟨2385778090363319380587701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6362074907635518348233869 2385778090363319380587701)
                ·
                  refine ⟨223666695971561191930097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2385778090363319380587701 223666695971561191930097)
                  ·
                    rfl

theorem cell21_980076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_980076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_980076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_980076 prefixEnd_980076 := by exact prefixLift 980076
  have htrace : WordTrace (prefixWord ++ tailWord_980076) baseStart_980076 baseEnd_980076 := by
    simpa [prefixWord, tailWord_980076, baseEnd_980076] using wordTrace_append hprefix tailTrace_980076
  have hstable : (prefixWord ++ tailWord_980076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980076).length < 2 ^ (prefixWord ++ tailWord_980076).sum := by decide
  have hdescent : baseEnd_980076 < baseStart_980076 := by decide
  rcases family_descends (prefixWord ++ tailWord_980076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980110 : List Nat := [4, 1, 1, 3, 2, 1, 1, 5, 3]
def baseStart_980110 : Nat := 118140960795 + 980110 * 2 ^ 59
def prefixEnd_980110 : Nat := 4983230072969 + 3 ^ 40 * 980110 * 2
def baseEnd_980110 : Nat := 223674455234784688363361

theorem tailTrace_980110 : CollatzResearch.WordTrace tailWord_980110 prefixEnd_980110 223674455234784688363361 := by
  unfold tailWord_980110
  simp only [CollatzResearch.WordTrace]
  refine ⟨4468443559904541788319223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23831698986157556204369189 4468443559904541788319223)
  ·
    refine ⟨6702665339856812682478835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4468443559904541788319223 6702665339856812682478835)
    ·
      refine ⟨10053998009785219023718253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6702665339856812682478835 10053998009785219023718253)
      ·
        refine ⟨3770249253669457133894345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10053998009785219023718253 3770249253669457133894345)
        ·
          refine ⟨2827686940252092850420759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3770249253669457133894345 2827686940252092850420759)
          ·
            refine ⟨4241530410378139275631139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2827686940252092850420759 4241530410378139275631139)
            ·
              refine ⟨6362295615567208913446709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4241530410378139275631139 6362295615567208913446709)
              ·
                refine ⟨596465213959425835635629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6362295615567208913446709 596465213959425835635629)
                ·
                  refine ⟨223674455234784688363361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 596465213959425835635629 223674455234784688363361)
                  ·
                    rfl

theorem cell21_980110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 5, 3].length) (baseStart_980110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_980110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_980110 prefixEnd_980110 := by exact prefixLift 980110
  have htrace : WordTrace (prefixWord ++ tailWord_980110) baseStart_980110 baseEnd_980110 := by
    simpa [prefixWord, tailWord_980110, baseEnd_980110] using wordTrace_append hprefix tailTrace_980110
  have hstable : (prefixWord ++ tailWord_980110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980110).length < 2 ^ (prefixWord ++ tailWord_980110).sum := by decide
  have hdescent : baseEnd_980110 < baseStart_980110 := by decide
  rcases family_descends (prefixWord ++ tailWord_980110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980124 : List Nat := [2, 2, 3, 2, 1, 2, 3, 2, 4]
def baseStart_980124 : Nat := 118140960795 + 980124 * 2 ^ 59
def prefixEnd_980124 : Nat := 4983230072969 + 3 ^ 40 * 980124 * 2
def baseEnd_980124 : Nat := 223677650225523775129999

theorem tailTrace_980124 : CollatzResearch.WordTrace tailWord_980124 prefixEnd_980124 223677650225523775129999 := by
  unfold tailWord_980124
  simp only [CollatzResearch.WordTrace]
  refine ⟨17874029550592807348781713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23832039400790409798375617 17874029550592807348781713)
  ·
    refine ⟨13405522162944605511586285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17874029550592807348781713 13405522162944605511586285)
    ·
      refine ⟨5027070811104227066844857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13405522162944605511586285 5027070811104227066844857)
      ·
        refine ⟨3770303108328170300133643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5027070811104227066844857 3770303108328170300133643)
        ·
          refine ⟨5655454662492255450200465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3770303108328170300133643 5655454662492255450200465)
          ·
            refine ⟨4241590996869191587650349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5655454662492255450200465 4241590996869191587650349)
            ·
              refine ⟨1590596623825946845368881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4241590996869191587650349 1590596623825946845368881)
              ·
                refine ⟨1192947467869460134026661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1590596623825946845368881 1192947467869460134026661)
                ·
                  refine ⟨223677650225523775129999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1192947467869460134026661 223677650225523775129999)
                  ·
                    rfl

theorem cell21_980124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2, 4].length) (baseStart_980124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_980124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_980124 prefixEnd_980124 := by exact prefixLift 980124
  have htrace : WordTrace (prefixWord ++ tailWord_980124) baseStart_980124 baseEnd_980124 := by
    simpa [prefixWord, tailWord_980124, baseEnd_980124] using wordTrace_append hprefix tailTrace_980124
  have hstable : (prefixWord ++ tailWord_980124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980124).length < 2 ^ (prefixWord ++ tailWord_980124).sum := by decide
  have hdescent : baseEnd_980124 < baseStart_980124 := by decide
  rcases family_descends (prefixWord ++ tailWord_980124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980259 : List Nat := [1, 1, 1, 4, 2, 3, 2, 3, 4]
def baseStart_980259 : Nat := 118140960795 + 980259 * 2 ^ 59
def prefixEnd_980259 : Nat := 4983230072969 + 3 ^ 40 * 980259 * 2
def baseEnd_980259 : Nat := 223708459064793540379723

theorem tailTrace_980259 : CollatzResearch.WordTrace tailWord_980259 prefixEnd_980259 223708459064793540379723 := by
  unfold tailWord_980259
  simp only [CollatzResearch.WordTrace]
  refine ⟨35752982955696532753727831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23835321970464355169151887 35752982955696532753727831)
  ·
    refine ⟨53629474433544799130591747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35752982955696532753727831 53629474433544799130591747)
    ·
      refine ⟨80444211650317198695887621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53629474433544799130591747 80444211650317198695887621)
      ·
        refine ⟨15083289684434474755478929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80444211650317198695887621 15083289684434474755478929)
        ·
          refine ⟨11312467263325856066609197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15083289684434474755478929 11312467263325856066609197)
          ·
            refine ⟨4242175223747196024978449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11312467263325856066609197 4242175223747196024978449)
            ·
              refine ⟨3181631417810397018733837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4242175223747196024978449 3181631417810397018733837)
              ·
                refine ⟨1193111781678898882025189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3181631417810397018733837 1193111781678898882025189)
                ·
                  refine ⟨223708459064793540379723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1193111781678898882025189 223708459064793540379723)
                  ·
                    rfl

theorem cell21_980259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3, 4].length) (baseStart_980259 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_980259 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_980259 prefixEnd_980259 := by exact prefixLift 980259
  have htrace : WordTrace (prefixWord ++ tailWord_980259) baseStart_980259 baseEnd_980259 := by
    simpa [prefixWord, tailWord_980259, baseEnd_980259] using wordTrace_append hprefix tailTrace_980259
  have hstable : (prefixWord ++ tailWord_980259).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980259).length < 2 ^ (prefixWord ++ tailWord_980259).sum := by decide
  have hdescent : baseEnd_980259 < baseStart_980259 := by decide
  rcases family_descends (prefixWord ++ tailWord_980259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980304 : List Nat := [2, 1, 1, 1, 1, 5, 4, 1, 5]
def baseStart_980304 : Nat := 118140960795 + 980304 * 2 ^ 59
def prefixEnd_980304 : Nat := 4983230072969 + 3 ^ 40 * 980304 * 2
def baseEnd_980304 : Nat := 223718728677883462129631

theorem tailTrace_980304 : CollatzResearch.WordTrace tailWord_980304 prefixEnd_980304 223718728677883462129631 := by
  unfold tailWord_980304
  simp only [CollatzResearch.WordTrace]
  refine ⟨17877312120266752719557983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23836416160355670292743977 17877312120266752719557983)
  ·
    refine ⟨26815968180400129079336975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17877312120266752719557983 26815968180400129079336975)
    ·
      refine ⟨40223952270600193619005463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26815968180400129079336975 40223952270600193619005463)
      ·
        refine ⟨60335928405900290428508195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40223952270600193619005463 60335928405900290428508195)
        ·
          refine ⟨90503892608850435642762293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60335928405900290428508195 90503892608850435642762293)
          ·
            refine ⟨8484739932079728341508965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90503892608850435642762293 8484739932079728341508965)
            ·
              refine ⟨1590888737264949064032931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8484739932079728341508965 1590888737264949064032931)
              ·
                refine ⟨2386333105897423596049397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1590888737264949064032931 2386333105897423596049397)
                ·
                  refine ⟨223718728677883462129631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2386333105897423596049397 223718728677883462129631)
                  ·
                    rfl

theorem cell21_980304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 5].length) (baseStart_980304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_980304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_980304 prefixEnd_980304 := by exact prefixLift 980304
  have htrace : WordTrace (prefixWord ++ tailWord_980304) baseStart_980304 baseEnd_980304 := by
    simpa [prefixWord, tailWord_980304, baseEnd_980304] using wordTrace_append hprefix tailTrace_980304
  have hstable : (prefixWord ++ tailWord_980304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980304).length < 2 ^ (prefixWord ++ tailWord_980304).sum := by decide
  have hdescent : baseEnd_980304 < baseStart_980304 := by decide
  rcases family_descends (prefixWord ++ tailWord_980304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980442 : List Nat := [3, 1, 1, 2, 3, 3, 3, 5]
def baseStart_980442 : Nat := 118140960795 + 980442 * 2 ^ 59
def prefixEnd_980442 : Nat := 4983230072969 + 3 ^ 40 * 980442 * 2
def baseEnd_980442 : Nat := 74583407386008629609783

theorem tailTrace_980442 : CollatzResearch.WordTrace tailWord_980442 prefixEnd_980442 74583407386008629609783 := by
  unfold tailWord_980442
  simp only [CollatzResearch.WordTrace]
  refine ⟨8939914378508388751909895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23839771676022370005093053 8939914378508388751909895)
  ·
    refine ⟨13409871567762583127864843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8939914378508388751909895 13409871567762583127864843)
    ·
      refine ⟨20114807351643874691797265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13409871567762583127864843 20114807351643874691797265)
      ·
        refine ⟨15086105513732906018847949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20114807351643874691797265 15086105513732906018847949)
        ·
          refine ⟨5657289567649839757067981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15086105513732906018847949 5657289567649839757067981)
          ·
            refine ⟨2121483587868689908900493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5657289567649839757067981 2121483587868689908900493)
            ·
              refine ⟨795556345450758715837685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2121483587868689908900493 795556345450758715837685)
              ·
                refine ⟨74583407386008629609783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 795556345450758715837685 74583407386008629609783)
                ·
                  rfl

theorem cell21_980442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 5].length) (baseStart_980442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_980442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_980442 prefixEnd_980442 := by exact prefixLift 980442
  have htrace : WordTrace (prefixWord ++ tailWord_980442) baseStart_980442 baseEnd_980442 := by
    simpa [prefixWord, tailWord_980442, baseEnd_980442] using wordTrace_append hprefix tailTrace_980442
  have hstable : (prefixWord ++ tailWord_980442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980442).length < 2 ^ (prefixWord ++ tailWord_980442).sum := by decide
  have hdescent : baseEnd_980442 < baseStart_980442 := by decide
  rcases family_descends (prefixWord ++ tailWord_980442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980493 : List Nat := [1, 7, 1, 1, 2, 2, 2, 5]
def baseStart_980493 : Nat := 118140960795 + 980493 * 2 ^ 59
def prefixEnd_980493 : Nat := 4983230072969 + 3 ^ 40 * 980493 * 2
def baseEnd_980493 : Nat := 74587287017620377826415

theorem tailTrace_980493 : CollatzResearch.WordTrace tailWord_980493 prefixEnd_980493 74587287017620377826415 := by
  unfold tailWord_980493
  simp only [CollatzResearch.WordTrace]
  refine ⟨35761517636848790717746133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23841011757899193811830755 35761517636848790717746133)
  ·
    refine ⟨838160569613643532447175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 35761517636848790717746133 838160569613643532447175)
    ·
      refine ⟨1257240854420465298670763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 838160569613643532447175 1257240854420465298670763)
      ·
        refine ⟨1885861281630697948006145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1257240854420465298670763 1885861281630697948006145)
        ·
          refine ⟨1414395961223023461004609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1885861281630697948006145 1414395961223023461004609)
          ·
            refine ⟨1060796970917267595753457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1414395961223023461004609 1060796970917267595753457)
            ·
              refine ⟨795597728187950696815093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1060796970917267595753457 795597728187950696815093)
              ·
                refine ⟨74587287017620377826415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 795597728187950696815093 74587287017620377826415)
                ·
                  rfl

theorem cell21_980493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 5].length) (baseStart_980493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_980493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_980493 prefixEnd_980493 := by exact prefixLift 980493
  have htrace : WordTrace (prefixWord ++ tailWord_980493) baseStart_980493 baseEnd_980493 := by
    simpa [prefixWord, tailWord_980493, baseEnd_980493] using wordTrace_append hprefix tailTrace_980493
  have hstable : (prefixWord ++ tailWord_980493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980493).length < 2 ^ (prefixWord ++ tailWord_980493).sum := by decide
  have hdescent : baseEnd_980493 < baseStart_980493 := by decide
  rcases family_descends (prefixWord ++ tailWord_980493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980501 : List Nat := [1, 3, 2, 1, 3, 3, 1, 7]
def baseStart_980501 : Nat := 118140960795 + 980501 * 2 ^ 59
def prefixEnd_980501 : Nat := 4983230072969 + 3 ^ 40 * 980501 * 2
def baseEnd_980501 : Nat := 74587895587284965781965

theorem tailTrace_980501 : CollatzResearch.WordTrace tailWord_980501 prefixEnd_980501 74587895587284965781965 := by
  unfold tailWord_980501
  simp only [CollatzResearch.WordTrace]
  refine ⟨35761809420819808084037357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23841206280546538722691571 35761809420819808084037357)
  ·
    refine ⟨13410678532807428031514009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35761809420819808084037357 13410678532807428031514009)
    ·
      refine ⟨10058008899605571023635507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13410678532807428031514009 10058008899605571023635507)
      ·
        refine ⟨15087013349408356535453261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10058008899605571023635507 15087013349408356535453261)
        ·
          refine ⟨5657630006028133700794973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15087013349408356535453261 5657630006028133700794973)
          ·
            refine ⟨2121611252260550137798115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5657630006028133700794973 2121611252260550137798115)
            ·
              refine ⟨3182416878390825206697173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2121611252260550137798115 3182416878390825206697173)
              ·
                refine ⟨74587895587284965781965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3182416878390825206697173 74587895587284965781965)
                ·
                  rfl

theorem cell21_980501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 7].length) (baseStart_980501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_980501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_980501 prefixEnd_980501 := by exact prefixLift 980501
  have htrace : WordTrace (prefixWord ++ tailWord_980501) baseStart_980501 baseEnd_980501 := by
    simpa [prefixWord, tailWord_980501, baseEnd_980501] using wordTrace_append hprefix tailTrace_980501
  have hstable : (prefixWord ++ tailWord_980501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980501).length < 2 ^ (prefixWord ++ tailWord_980501).sum := by decide
  have hdescent : baseEnd_980501 < baseStart_980501 := by decide
  rcases family_descends (prefixWord ++ tailWord_980501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980560 : List Nat := [2, 1, 1, 1, 1, 3, 3, 9]
def baseStart_980560 : Nat := 118140960795 + 980560 * 2 ^ 59
def prefixEnd_980560 : Nat := 4983230072969 + 3 ^ 40 * 980560 * 2
def baseEnd_980560 : Nat := 74592383788561301954147

theorem tailTrace_980560 : CollatzResearch.WordTrace tailWord_980560 prefixEnd_980560 74592383788561301954147 := by
  unfold tailWord_980560
  simp only [CollatzResearch.WordTrace]
  refine ⟨17881980663803030580217567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23842640885070707440290089 17881980663803030580217567)
  ·
    refine ⟨26822970995704545870326351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17881980663803030580217567 26822970995704545870326351)
    ·
      refine ⟨40234456493556818805489527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26822970995704545870326351 40234456493556818805489527)
      ·
        refine ⟨60351684740335228208234291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40234456493556818805489527 60351684740335228208234291)
        ·
          refine ⟨90527527110502842312351437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60351684740335228208234291 90527527110502842312351437)
          ·
            refine ⟨33947822666438565867131789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90527527110502842312351437 33947822666438565867131789)
            ·
              refine ⟨12730433499914462200174421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33947822666438565867131789 12730433499914462200174421)
              ·
                refine ⟨74592383788561301954147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12730433499914462200174421 74592383788561301954147)
                ·
                  rfl

theorem cell21_980560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 9].length) (baseStart_980560 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_980560 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_980560 prefixEnd_980560 := by exact prefixLift 980560
  have htrace : WordTrace (prefixWord ++ tailWord_980560) baseStart_980560 baseEnd_980560 := by
    simpa [prefixWord, tailWord_980560, baseEnd_980560] using wordTrace_append hprefix tailTrace_980560
  have hstable : (prefixWord ++ tailWord_980560).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980560).length < 2 ^ (prefixWord ++ tailWord_980560).sum := by decide
  have hdescent : baseEnd_980560 < baseStart_980560 := by decide
  rcases family_descends (prefixWord ++ tailWord_980560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980591 : List Nat := [1, 1, 2, 1, 3, 2, 1, 5, 5]
def baseStart_980591 : Nat := 118140960795 + 980591 * 2 ^ 59
def prefixEnd_980591 : Nat := 4983230072969 + 3 ^ 40 * 980591 * 2
def baseEnd_980591 : Nat := 223784225988034740845711

theorem tailTrace_980591 : CollatzResearch.WordTrace tailWord_980591 prefixEnd_980591 223784225988034740845711 := by
  unfold tailWord_980591
  simp only [CollatzResearch.WordTrace]
  refine ⟨35765091990493753454813627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23843394660329168969875751 35765091990493753454813627)
  ·
    refine ⟨53647637985740630182220441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35765091990493753454813627 53647637985740630182220441)
    ·
      refine ⟨40235728489305472636665331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53647637985740630182220441 40235728489305472636665331)
      ·
        refine ⟨60353592733958208954997997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40235728489305472636665331 60353592733958208954997997)
        ·
          refine ⟨22632597275234328358124249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60353592733958208954997997 22632597275234328358124249)
          ·
            refine ⟨16974447956425746268593187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22632597275234328358124249 16974447956425746268593187)
            ·
              refine ⟨25461671934638619402889781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16974447956425746268593187 25461671934638619402889781)
              ·
                refine ⟨2387031743872370569020917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25461671934638619402889781 2387031743872370569020917)
                ·
                  refine ⟨223784225988034740845711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2387031743872370569020917 223784225988034740845711)
                  ·
                    rfl

theorem cell21_980591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 5].length) (baseStart_980591 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_980591 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_980591 prefixEnd_980591 := by exact prefixLift 980591
  have htrace : WordTrace (prefixWord ++ tailWord_980591) baseStart_980591 baseEnd_980591 := by
    simpa [prefixWord, tailWord_980591, baseEnd_980591] using wordTrace_append hprefix tailTrace_980591
  have hstable : (prefixWord ++ tailWord_980591).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980591).length < 2 ^ (prefixWord ++ tailWord_980591).sum := by decide
  have hdescent : baseEnd_980591 < baseStart_980591 := by decide
  rcases family_descends (prefixWord ++ tailWord_980591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980594 : List Nat := [3, 2, 1, 2, 3, 3, 1, 6]
def baseStart_980594 : Nat := 118140960795 + 980594 * 2 ^ 59
def prefixEnd_980594 : Nat := 4983230072969 + 3 ^ 40 * 980594 * 2
def baseEnd_980594 : Nat := 74594970209635800765235

theorem tailTrace_980594 : CollatzResearch.WordTrace tailWord_980594 prefixEnd_980594 74594970209635800765235 := by
  unfold tailWord_980594
  simp only [CollatzResearch.WordTrace]
  refine ⟨8941300352370721241793209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23843467606321923311448557 8941300352370721241793209)
  ·
    refine ⟨6705975264278040931344907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8941300352370721241793209 6705975264278040931344907)
    ·
      refine ⟨10058962896417061397017361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6705975264278040931344907 10058962896417061397017361)
      ·
        refine ⟨7544222172312796047763021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10058962896417061397017361 7544222172312796047763021)
        ·
          refine ⟨2829083314617298517911133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7544222172312796047763021 2829083314617298517911133)
          ·
            refine ⟨1060906242981486944216675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2829083314617298517911133 1060906242981486944216675)
            ·
              refine ⟨1591359364472230416325013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1060906242981486944216675 1591359364472230416325013)
              ·
                refine ⟨74594970209635800765235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1591359364472230416325013 74594970209635800765235)
                ·
                  rfl

theorem cell21_980594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 6].length) (baseStart_980594 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_980594 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_980594 prefixEnd_980594 := by exact prefixLift 980594
  have htrace : WordTrace (prefixWord ++ tailWord_980594) baseStart_980594 baseEnd_980594 := by
    simpa [prefixWord, tailWord_980594, baseEnd_980594] using wordTrace_append hprefix tailTrace_980594
  have hstable : (prefixWord ++ tailWord_980594).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980594).length < 2 ^ (prefixWord ++ tailWord_980594).sum := by decide
  have hdescent : baseEnd_980594 < baseStart_980594 := by decide
  rcases family_descends (prefixWord ++ tailWord_980594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980642 : List Nat := [3, 3, 1, 4, 1, 1, 2, 1, 5]
def baseStart_980642 : Nat := 118140960795 + 980642 * 2 ^ 59
def prefixEnd_980642 : Nat := 4983230072969 + 3 ^ 40 * 980642 * 2
def baseEnd_980642 : Nat := 223795864882869985495607

theorem tailTrace_980642 : CollatzResearch.WordTrace tailWord_980642 prefixEnd_980642 223795864882869985495607 := by
  unfold tailWord_980642
  simp only [CollatzResearch.WordTrace]
  refine ⟨8941738028327247291230045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23844634742205992776613453 8941738028327247291230045)
  ·
    refine ⟨3353151760622717734211267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8941738028327247291230045 3353151760622717734211267)
    ·
      refine ⟨5029727640934076601316901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3353151760622717734211267 5029727640934076601316901)
      ·
        refine ⟨943073932675139362746919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5029727640934076601316901 943073932675139362746919)
        ·
          refine ⟨1414610899012709044120379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 943073932675139362746919 1414610899012709044120379)
          ·
            refine ⟨2121916348519063566180569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1414610899012709044120379 2121916348519063566180569)
            ·
              refine ⟨1591437261389297674635427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2121916348519063566180569 1591437261389297674635427)
              ·
                refine ⟨2387155892083946511953141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1591437261389297674635427 2387155892083946511953141)
                ·
                  refine ⟨223795864882869985495607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2387155892083946511953141 223795864882869985495607)
                  ·
                    rfl

theorem cell21_980642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_980642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_980642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_980642 prefixEnd_980642 := by exact prefixLift 980642
  have htrace : WordTrace (prefixWord ++ tailWord_980642) baseStart_980642 baseEnd_980642 := by
    simpa [prefixWord, tailWord_980642, baseEnd_980642] using wordTrace_append hprefix tailTrace_980642
  have hstable : (prefixWord ++ tailWord_980642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980642).length < 2 ^ (prefixWord ++ tailWord_980642).sum := by decide
  have hdescent : baseEnd_980642 < baseStart_980642 := by decide
  rcases family_descends (prefixWord ++ tailWord_980642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980653 : List Nat := [1, 5, 2, 1, 1, 1, 2, 8]
def baseStart_980653 : Nat := 118140960795 + 980653 * 2 ^ 59
def prefixEnd_980653 : Nat := 4983230072969 + 3 ^ 40 * 980653 * 2
def baseEnd_980653 : Nat := 74599458410912136937417

theorem tailTrace_980653 : CollatzResearch.WordTrace tailWord_980653 prefixEnd_980653 74599458410912136937417 := by
  unfold tailWord_980653
  simp only [CollatzResearch.WordTrace]
  refine ⟨35767353316269138043570613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23844902210846092029047075 35767353316269138043570613)
  ·
    refine ⟨3353189373400231691584745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35767353316269138043570613 3353189373400231691584745)
    ·
      refine ⟨2514892030050173768688559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3353189373400231691584745 2514892030050173768688559)
      ·
        refine ⟨3772338045075260653032839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2514892030050173768688559 3772338045075260653032839)
        ·
          refine ⟨5658507067612890979549259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3772338045075260653032839 5658507067612890979549259)
          ·
            refine ⟨8487760601419336469323889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5658507067612890979549259 8487760601419336469323889)
            ·
              refine ⟨6365820451064502351992917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8487760601419336469323889 6365820451064502351992917)
              ·
                refine ⟨74599458410912136937417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6365820451064502351992917 74599458410912136937417)
                ·
                  rfl

theorem cell21_980653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 8].length) (baseStart_980653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_980653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_980653 prefixEnd_980653 := by exact prefixLift 980653
  have htrace : WordTrace (prefixWord ++ tailWord_980653) baseStart_980653 baseEnd_980653 := by
    simpa [prefixWord, tailWord_980653, baseEnd_980653] using wordTrace_append hprefix tailTrace_980653
  have hstable : (prefixWord ++ tailWord_980653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980653).length < 2 ^ (prefixWord ++ tailWord_980653).sum := by decide
  have hdescent : baseEnd_980653 < baseStart_980653 := by decide
  rcases family_descends (prefixWord ++ tailWord_980653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980670 : List Nat := [4, 2, 1, 1, 2, 2, 4, 5]
def baseStart_980670 : Nat := 118140960795 + 980670 * 2 ^ 59
def prefixEnd_980670 : Nat := 4983230072969 + 3 ^ 40 * 980670 * 2
def baseEnd_980670 : Nat := 74600751621449386342961

theorem tailTrace_980670 : CollatzResearch.WordTrace tailWord_980670 prefixEnd_980670 74600751621449386342961 := by
  unfold tailWord_980670
  simp only [CollatzResearch.WordTrace]
  refine ⟨4470996669650943743367433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23845315571471699964626309 4470996669650943743367433)
  ·
    refine ⟨3353247502238207807525575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4470996669650943743367433 3353247502238207807525575)
    ·
      refine ⟨5029871253357311711288363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3353247502238207807525575 5029871253357311711288363)
      ·
        refine ⟨7544806880035967566932545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5029871253357311711288363 7544806880035967566932545)
        ·
          refine ⟨5658605160026975675199409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7544806880035967566932545 5658605160026975675199409)
          ·
            refine ⟨4243953870020231756399557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5658605160026975675199409 4243953870020231756399557)
            ·
              refine ⟨795741350628793454324917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4243953870020231756399557 795741350628793454324917)
              ·
                refine ⟨74600751621449386342961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 795741350628793454324917 74600751621449386342961)
                ·
                  rfl

theorem cell21_980670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_980670 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_980670 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_980670 prefixEnd_980670 := by exact prefixLift 980670
  have htrace : WordTrace (prefixWord ++ tailWord_980670) baseStart_980670 baseEnd_980670 := by
    simpa [prefixWord, tailWord_980670, baseEnd_980670] using wordTrace_append hprefix tailTrace_980670
  have hstable : (prefixWord ++ tailWord_980670).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980670).length < 2 ^ (prefixWord ++ tailWord_980670).sum := by decide
  have hdescent : baseEnd_980670 < baseStart_980670 := by decide
  rcases family_descends (prefixWord ++ tailWord_980670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980698 : List Nat := [3, 1, 1, 2, 2, 3, 2, 1, 6]
def baseStart_980698 : Nat := 118140960795 + 980698 * 2 ^ 59
def prefixEnd_980698 : Nat := 4983230072969 + 3 ^ 40 * 980698 * 2
def baseEnd_980698 : Nat := 223808644845826332562159

theorem tailTrace_980698 : CollatzResearch.WordTrace tailWord_980698 prefixEnd_980698 223808644845826332562159 := by
  unfold tailWord_980698
  simp only [CollatzResearch.WordTrace]
  refine ⟨8942248650276527682239687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23845996400737407152639165 8942248650276527682239687)
  ·
    refine ⟨13413372975414791523359531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8942248650276527682239687 13413372975414791523359531)
    ·
      refine ⟨20120059463122187285039297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13413372975414791523359531 20120059463122187285039297)
      ·
        refine ⟨15090044597341640463779473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20120059463122187285039297 15090044597341640463779473)
        ·
          refine ⟨11317533448006230347834605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15090044597341640463779473 11317533448006230347834605)
          ·
            refine ⟨4244075043002336380437977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11317533448006230347834605 4244075043002336380437977)
            ·
              refine ⟨3183056282251752285328483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4244075043002336380437977 3183056282251752285328483)
              ·
                refine ⟨4774584423377628427992725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3183056282251752285328483 4774584423377628427992725)
                ·
                  refine ⟨223808644845826332562159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4774584423377628427992725 223808644845826332562159)
                  ·
                    rfl

theorem cell21_980698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_980698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_980698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_980698 prefixEnd_980698 := by exact prefixLift 980698
  have htrace : WordTrace (prefixWord ++ tailWord_980698) baseStart_980698 baseEnd_980698 := by
    simpa [prefixWord, tailWord_980698, baseEnd_980698] using wordTrace_append hprefix tailTrace_980698
  have hstable : (prefixWord ++ tailWord_980698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980698).length < 2 ^ (prefixWord ++ tailWord_980698).sum := by decide
  have hdescent : baseEnd_980698 < baseStart_980698 := by decide
  rcases family_descends (prefixWord ++ tailWord_980698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980715 : List Nat := [1, 1, 1, 1, 2, 4, 6, 1, 4]
def baseStart_980715 : Nat := 118140960795 + 980715 * 2 ^ 59
def prefixEnd_980715 : Nat := 4983230072969 + 3 ^ 40 * 980715 * 2
def baseEnd_980715 : Nat := 223812524477438080778791

theorem tailTrace_980715 : CollatzResearch.WordTrace tailWord_980715 prefixEnd_980715 223812524477438080778791 := by
  unfold tailWord_980715
  simp only [CollatzResearch.WordTrace]
  refine ⟨35769614642044522632327599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23846409761363015088218399 35769614642044522632327599)
  ·
    refine ⟨53654421963066783948491399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35769614642044522632327599 53654421963066783948491399)
    ·
      refine ⟨80481632944600175922737099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53654421963066783948491399 80481632944600175922737099)
      ·
        refine ⟨120722449416900263884105649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80481632944600175922737099 120722449416900263884105649)
        ·
          refine ⟨90541837062675197913079237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120722449416900263884105649 90541837062675197913079237)
          ·
            refine ⟨16976594449251599608702357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90541837062675197913079237 16976594449251599608702357)
            ·
              refine ⟨795777864808668731657923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16976594449251599608702357 795777864808668731657923)
              ·
                refine ⟨1193666797213003097486885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 795777864808668731657923 1193666797213003097486885)
                ·
                  refine ⟨223812524477438080778791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1193666797213003097486885 223812524477438080778791)
                  ·
                    rfl

theorem cell21_980715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 1, 4].length) (baseStart_980715 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_980715 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_980715 prefixEnd_980715 := by exact prefixLift 980715
  have htrace : WordTrace (prefixWord ++ tailWord_980715) baseStart_980715 baseEnd_980715 := by
    simpa [prefixWord, tailWord_980715, baseEnd_980715] using wordTrace_append hprefix tailTrace_980715
  have hstable : (prefixWord ++ tailWord_980715).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980715).length < 2 ^ (prefixWord ++ tailWord_980715).sum := by decide
  have hdescent : baseEnd_980715 < baseStart_980715 := by decide
  rcases family_descends (prefixWord ++ tailWord_980715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980884 : List Nat := [2, 4, 2, 1, 1, 2, 4, 1, 4]
def baseStart_980884 : Nat := 118140960795 + 980884 * 2 ^ 59
def prefixEnd_980884 : Nat := 4983230072969 + 3 ^ 40 * 980884 * 2
def baseEnd_980884 : Nat := 223851092579931342461779

theorem tailTrace_980884 : CollatzResearch.WordTrace tailWord_980884 prefixEnd_980884 223851092579931342461779 := by
  unfold tailWord_980884
  simp only [CollatzResearch.WordTrace]
  refine ⟨17887889289216132247614853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23850519052288176330153137 17887889289216132247614853)
  ·
    refine ⟨3353979241728024796427785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17887889289216132247614853 3353979241728024796427785)
    ·
      refine ⟨2515484431296018597320839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3353979241728024796427785 2515484431296018597320839)
      ·
        refine ⟨3773226646944027895981259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2515484431296018597320839 3773226646944027895981259)
        ·
          refine ⟨5659839970416041843971889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3773226646944027895981259 5659839970416041843971889)
          ·
            refine ⟨4244879977812031382978917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5659839970416041843971889 4244879977812031382978917)
            ·
              refine ⟨795914995839755884308547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4244879977812031382978917 795914995839755884308547)
              ·
                refine ⟨1193872493759633826462821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 795914995839755884308547 1193872493759633826462821)
                ·
                  refine ⟨223851092579931342461779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1193872493759633826462821 223851092579931342461779)
                  ·
                    rfl

theorem cell21_980884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_980884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_980884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_980884 prefixEnd_980884 := by exact prefixLift 980884
  have htrace : WordTrace (prefixWord ++ tailWord_980884) baseStart_980884 baseEnd_980884 := by
    simpa [prefixWord, tailWord_980884, baseEnd_980884] using wordTrace_append hprefix tailTrace_980884
  have hstable : (prefixWord ++ tailWord_980884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980884).length < 2 ^ (prefixWord ++ tailWord_980884).sum := by decide
  have hdescent : baseEnd_980884 < baseStart_980884 := by decide
  rcases family_descends (prefixWord ++ tailWord_980884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980988 : List Nat := [2, 2, 2, 1, 2, 2, 1, 6, 3]
def baseStart_980988 : Nat := 118140960795 + 980988 * 2 ^ 59
def prefixEnd_980988 : Nat := 4983230072969 + 3 ^ 40 * 980988 * 2
def baseEnd_980988 : Nat := 223874826796850272728233

theorem tailTrace_980988 : CollatzResearch.WordTrace tailWord_980988 prefixEnd_980988 223874826796850272728233 := by
  unfold tailWord_980988
  simp only [CollatzResearch.WordTrace]
  refine ⟨17889785885027745128507809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23853047846703660171343745 17889785885027745128507809)
  ·
    refine ⟨13417339413770808846380857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17889785885027745128507809 13417339413770808846380857)
    ·
      refine ⟨10063004560328106634785643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13417339413770808846380857 10063004560328106634785643)
      ·
        refine ⟨15094506840492159952178465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10063004560328106634785643 15094506840492159952178465)
        ·
          refine ⟨11320880130369119964133849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15094506840492159952178465 11320880130369119964133849)
          ·
            refine ⟨8490660097776839973100387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11320880130369119964133849 8490660097776839973100387)
            ·
              refine ⟨12735990146665259959650581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8490660097776839973100387 12735990146665259959650581)
              ·
                refine ⟨596999538124934060608621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12735990146665259959650581 596999538124934060608621)
                ·
                  refine ⟨223874826796850272728233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 596999538124934060608621 223874826796850272728233)
                  ·
                    rfl

theorem cell21_980988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 6, 3].length) (baseStart_980988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_980988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_980988 prefixEnd_980988 := by exact prefixLift 980988
  have htrace : WordTrace (prefixWord ++ tailWord_980988) baseStart_980988 baseEnd_980988 := by
    simpa [prefixWord, tailWord_980988, baseEnd_980988] using wordTrace_append hprefix tailTrace_980988
  have hstable : (prefixWord ++ tailWord_980988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980988).length < 2 ^ (prefixWord ++ tailWord_980988).sum := by decide
  have hdescent : baseEnd_980988 < baseStart_980988 := by decide
  rcases family_descends (prefixWord ++ tailWord_980988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981016 : List Nat := [2, 1, 2, 3, 2, 1, 3, 7]
def baseStart_981016 : Nat := 118140960795 + 981016 * 2 ^ 59
def prefixEnd_981016 : Nat := 4983230072969 + 3 ^ 40 * 981016 * 2
def baseEnd_981016 : Nat := 74627072259442815420503

theorem tailTrace_981016 : CollatzResearch.WordTrace tailWord_981016 prefixEnd_981016 74627072259442815420503 := by
  unfold tailWord_981016
  simp only [CollatzResearch.WordTrace]
  refine ⟨17890296506977025519517451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23853728675969367359356601 17890296506977025519517451)
  ·
    refine ⟨26835444760465538279276177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17890296506977025519517451 26835444760465538279276177)
    ·
      refine ⟨20126583570349153709457133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26835444760465538279276177 20126583570349153709457133)
      ·
        refine ⟨7547468838880932641046425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20126583570349153709457133 7547468838880932641046425)
        ·
          refine ⟨5660601629160699480784819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7547468838880932641046425 5660601629160699480784819)
          ·
            refine ⟨8490902443741049221177229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5660601629160699480784819 8490902443741049221177229)
            ·
              refine ⟨3184088416402893457941461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8490902443741049221177229 3184088416402893457941461)
              ·
                refine ⟨74627072259442815420503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3184088416402893457941461 74627072259442815420503)
                ·
                  rfl

theorem cell21_981016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 7].length) (baseStart_981016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_981016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_981016 prefixEnd_981016 := by exact prefixLift 981016
  have htrace : WordTrace (prefixWord ++ tailWord_981016) baseStart_981016 baseEnd_981016 := by
    simpa [prefixWord, tailWord_981016, baseEnd_981016] using wordTrace_append hprefix tailTrace_981016
  have hstable : (prefixWord ++ tailWord_981016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981016).length < 2 ^ (prefixWord ++ tailWord_981016).sum := by decide
  have hdescent : baseEnd_981016 < baseStart_981016 := by decide
  rcases family_descends (prefixWord ++ tailWord_981016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981047 : List Nat := [1, 1, 3, 1, 2, 2, 5, 1, 5]
def baseStart_981047 : Nat := 118140960795 + 981047 * 2 ^ 59
def prefixEnd_981047 : Nat := 4983230072969 + 3 ^ 40 * 981047 * 2
def baseEnd_981047 : Nat := 223888291400679281244779

theorem tailTrace_981047 : CollatzResearch.WordTrace tailWord_981047 prefixEnd_981047 223888291400679281244779 := by
  unfold tailWord_981047
  simp only [CollatzResearch.WordTrace]
  refine ⟨35781723676841743333413395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23854482451227828888942263 35781723676841743333413395)
  ·
    refine ⟨53672585515262615000120093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35781723676841743333413395 53672585515262615000120093)
    ·
      refine ⟨20127219568223480625045035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53672585515262615000120093 20127219568223480625045035)
      ·
        refine ⟨30190829352335220937567553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20127219568223480625045035 30190829352335220937567553)
        ·
          refine ⟨22643122014251415703175665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30190829352335220937567553 22643122014251415703175665)
          ·
            refine ⟨16982341510688561777381749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22643122014251415703175665 16982341510688561777381749)
            ·
              refine ⟨1592094516627052666629539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16982341510688561777381749 1592094516627052666629539)
              ·
                refine ⟨2388141774940578999944309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1592094516627052666629539 2388141774940578999944309)
                ·
                  refine ⟨223888291400679281244779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2388141774940578999944309 223888291400679281244779)
                  ·
                    rfl

theorem cell21_981047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 5].length) (baseStart_981047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_981047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_981047 prefixEnd_981047 := by exact prefixLift 981047
  have htrace : WordTrace (prefixWord ++ tailWord_981047) baseStart_981047 baseEnd_981047 := by
    simpa [prefixWord, tailWord_981047, baseEnd_981047] using wordTrace_append hprefix tailTrace_981047
  have hstable : (prefixWord ++ tailWord_981047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981047).length < 2 ^ (prefixWord ++ tailWord_981047).sum := by decide
  have hdescent : baseEnd_981047 < baseStart_981047 := by decide
  rcases family_descends (prefixWord ++ tailWord_981047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981123 : List Nat := [1, 1, 1, 3, 3, 4, 1, 2, 5]
def baseStart_981123 : Nat := 118140960795 + 981123 * 2 ^ 59
def prefixEnd_981123 : Nat := 4983230072969 + 3 ^ 40 * 981123 * 2
def baseEnd_981123 : Nat := 223905635636120037977957

theorem tailTrace_981123 : CollatzResearch.WordTrace tailWord_981123 prefixEnd_981123 223905635636120037977957 := by
  unfold tailWord_981123
  simp only [CollatzResearch.WordTrace]
  refine ⟨35784495624566408313180023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23856330416377605542120015 35784495624566408313180023)
  ·
    refine ⟨53676743436849612469770035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35784495624566408313180023 53676743436849612469770035)
    ·
      refine ⟨80515115155274418704655053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53676743436849612469770035 80515115155274418704655053)
      ·
        refine ⟨30193168183227907014245645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80515115155274418704655053 30193168183227907014245645)
        ·
          refine ⟨11322438068710465130342117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30193168183227907014245645 11322438068710465130342117)
          ·
            refine ⟨2122957137883212211939147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11322438068710465130342117 2122957137883212211939147)
            ·
              refine ⟨3184435706824818317908721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2122957137883212211939147 3184435706824818317908721)
              ·
                refine ⟨2388326780118613738431541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3184435706824818317908721 2388326780118613738431541)
                ·
                  refine ⟨223905635636120037977957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2388326780118613738431541 223905635636120037977957)
                  ·
                    rfl

theorem cell21_981123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 5].length) (baseStart_981123 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_981123 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_981123 prefixEnd_981123 := by exact prefixLift 981123
  have htrace : WordTrace (prefixWord ++ tailWord_981123) baseStart_981123 baseEnd_981123 := by
    simpa [prefixWord, tailWord_981123, baseEnd_981123] using wordTrace_append hprefix tailTrace_981123
  have hstable : (prefixWord ++ tailWord_981123).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981123).length < 2 ^ (prefixWord ++ tailWord_981123).sum := by decide
  have hdescent : baseEnd_981123 < baseStart_981123 := by decide
  rcases family_descends (prefixWord ++ tailWord_981123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981244 : List Nat := [2, 2, 2, 1, 4, 1, 2, 7]
def baseStart_981244 : Nat := 118140960795 + 981244 * 2 ^ 59
def prefixEnd_981244 : Nat := 4983230072969 + 3 ^ 40 * 981244 * 2
def baseEnd_981244 : Nat := 74644416494883572153681

theorem tailTrace_981244 : CollatzResearch.WordTrace tailWord_981244 prefixEnd_981244 74644416494883572153681 := by
  unfold tailWord_981244
  simp only [CollatzResearch.WordTrace]
  refine ⟨17894454428564022989167393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23859272571418697318889857 17894454428564022989167393)
  ·
    refine ⟨13420840821423017241875545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17894454428564022989167393 13420840821423017241875545)
    ·
      refine ⟨10065630616067262931406659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13420840821423017241875545 10065630616067262931406659)
      ·
        refine ⟨15098445924100894397109989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10065630616067262931406659 15098445924100894397109989)
        ·
          refine ⟨2830958610768917699458123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15098445924100894397109989 2830958610768917699458123)
          ·
            refine ⟨4246437916153376549187185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2830958610768917699458123 4246437916153376549187185)
            ·
              refine ⟨3184828437115032411890389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4246437916153376549187185 3184828437115032411890389)
              ·
                refine ⟨74644416494883572153681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3184828437115032411890389 74644416494883572153681)
                ·
                  rfl

theorem cell21_981244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 7].length) (baseStart_981244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_981244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_981244 prefixEnd_981244 := by exact prefixLift 981244
  have htrace : WordTrace (prefixWord ++ tailWord_981244) baseStart_981244 baseEnd_981244 := by
    simpa [prefixWord, tailWord_981244, baseEnd_981244] using wordTrace_append hprefix tailTrace_981244
  have hstable : (prefixWord ++ tailWord_981244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981244).length < 2 ^ (prefixWord ++ tailWord_981244).sum := by decide
  have hdescent : baseEnd_981244 < baseStart_981244 := by decide
  rcases family_descends (prefixWord ++ tailWord_981244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981278 : List Nat := [4, 3, 2, 1, 1, 1, 3, 6]
def baseStart_981278 : Nat := 118140960795 + 981278 * 2 ^ 59
def prefixEnd_981278 : Nat := 4983230072969 + 3 ^ 40 * 981278 * 2
def baseEnd_981278 : Nat := 74647002915958070964769

theorem tailTrace_981278 : CollatzResearch.WordTrace tailWord_981278 prefixEnd_981278 74647002915958070964769 := by
  unfold tailWord_981278
  simp only [CollatzResearch.WordTrace]
  refine ⟨4473768617375608723134061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23860099292669913190048325 4473768617375608723134061)
  ·
    refine ⟨1677663231515853271175273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4473768617375608723134061 1677663231515853271175273)
    ·
      refine ⟨1258247423636889953381455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1677663231515853271175273 1258247423636889953381455)
      ·
        refine ⟨1887371135455334930072183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1258247423636889953381455 1887371135455334930072183)
        ·
          refine ⟨2831056703183002395108275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1887371135455334930072183 2831056703183002395108275)
          ·
            refine ⟨4246585054774503592662413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2831056703183002395108275 4246585054774503592662413)
            ·
              refine ⟨1592469395540438847248405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4246585054774503592662413 1592469395540438847248405)
              ·
                refine ⟨74647002915958070964769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1592469395540438847248405 74647002915958070964769)
                ·
                  rfl

theorem cell21_981278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_981278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_981278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_981278 prefixEnd_981278 := by exact prefixLift 981278
  have htrace : WordTrace (prefixWord ++ tailWord_981278) baseStart_981278 baseEnd_981278 := by
    simpa [prefixWord, tailWord_981278, baseEnd_981278] using wordTrace_append hprefix tailTrace_981278
  have hstable : (prefixWord ++ tailWord_981278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981278).length < 2 ^ (prefixWord ++ tailWord_981278).sum := by decide
  have hdescent : baseEnd_981278 < baseStart_981278 := by decide
  rcases family_descends (prefixWord ++ tailWord_981278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981303 : List Nat := [1, 1, 3, 1, 2, 1, 1, 11]
def baseStart_981303 : Nat := 118140960795 + 981303 * 2 ^ 59
def prefixEnd_981303 : Nat := 4983230072969 + 3 ^ 40 * 981303 * 2
def baseEnd_981303 : Nat := 74648904696159908325863

theorem tailTrace_981303 : CollatzResearch.WordTrace tailWord_981303 prefixEnd_981303 74648904696159908325863 := by
  unfold tailWord_981303
  simp only [CollatzResearch.WordTrace]
  refine ⟨35791060763914299054732563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23860707175942866036488375 35791060763914299054732563)
  ·
    refine ⟨53686591145871448582098845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35791060763914299054732563 53686591145871448582098845)
    ·
      refine ⟨20132471679701793218287067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53686591145871448582098845 20132471679701793218287067)
      ·
        refine ⟨30198707519552689827430601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20132471679701793218287067 30198707519552689827430601)
        ·
          refine ⟨22649030639664517370572951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30198707519552689827430601 22649030639664517370572951)
          ·
            refine ⟨33973545959496776055859427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22649030639664517370572951 33973545959496776055859427)
            ·
              refine ⟨50960318939245164083789141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33973545959496776055859427 50960318939245164083789141)
              ·
                refine ⟨74648904696159908325863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 50960318939245164083789141 74648904696159908325863)
                ·
                  rfl

theorem cell21_981303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 11].length) (baseStart_981303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_981303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_981303 prefixEnd_981303 := by exact prefixLift 981303
  have htrace : WordTrace (prefixWord ++ tailWord_981303) baseStart_981303 baseEnd_981303 := by
    simpa [prefixWord, tailWord_981303, baseEnd_981303] using wordTrace_append hprefix tailTrace_981303
  have hstable : (prefixWord ++ tailWord_981303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981303).length < 2 ^ (prefixWord ++ tailWord_981303).sum := by decide
  have hdescent : baseEnd_981303 < baseStart_981303 := by decide
  rcases family_descends (prefixWord ++ tailWord_981303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981351 : List Nat := [1, 1, 5, 1, 3, 1, 2, 2, 5]
def baseStart_981351 : Nat := 118140960795 + 981351 * 2 ^ 59
def prefixEnd_981351 : Nat := 4983230072969 + 3 ^ 40 * 981351 * 2
def baseEnd_981351 : Nat := 223957668342442308177491

theorem tailTrace_981351 : CollatzResearch.WordTrace tailWord_981351 prefixEnd_981351 223957668342442308177491 := by
  unfold tailWord_981351
  simp only [CollatzResearch.WordTrace]
  refine ⟨35792811467740403252479907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23861874311826935501653271 35792811467740403252479907)
  ·
    refine ⟨53689217201610604878719861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35792811467740403252479907 53689217201610604878719861)
    ·
      refine ⟨5033364112650994207379987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53689217201610604878719861 5033364112650994207379987)
      ·
        refine ⟨7550046168976491311069981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5033364112650994207379987 7550046168976491311069981)
        ·
          refine ⟨2831267313366184241651243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7550046168976491311069981 2831267313366184241651243)
          ·
            refine ⟨4246900970049276362476865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2831267313366184241651243 4246900970049276362476865)
            ·
              refine ⟨3185175727536957271857649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4246900970049276362476865 3185175727536957271857649)
              ·
                refine ⟨2388881795652717953893237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3185175727536957271857649 2388881795652717953893237)
                ·
                  refine ⟨223957668342442308177491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2388881795652717953893237 223957668342442308177491)
                  ·
                    rfl

theorem cell21_981351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 5].length) (baseStart_981351 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_981351 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_981351 prefixEnd_981351 := by exact prefixLift 981351
  have htrace : WordTrace (prefixWord ++ tailWord_981351) baseStart_981351 baseEnd_981351 := by
    simpa [prefixWord, tailWord_981351, baseEnd_981351] using wordTrace_append hprefix tailTrace_981351
  have hstable : (prefixWord ++ tailWord_981351).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981351).length < 2 ^ (prefixWord ++ tailWord_981351).sum := by decide
  have hdescent : baseEnd_981351 < baseStart_981351 := by decide
  rcases family_descends (prefixWord ++ tailWord_981351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981354 : List Nat := [3, 1, 3, 3, 1, 3, 2, 5]
def baseStart_981354 : Nat := 118140960795 + 981354 * 2 ^ 59
def prefixEnd_981354 : Nat := 4983230072969 + 3 ^ 40 * 981354 * 2
def baseEnd_981354 : Nat := 74652784327771656542495

theorem tailTrace_981354 : CollatzResearch.WordTrace tailWord_981354 prefixEnd_981354 74652784327771656542495 := by
  unfold tailWord_981354
  simp only [CollatzResearch.WordTrace]
  refine ⟨8948230221682383691209779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23861947257819689843226077 8948230221682383691209779)
  ·
    refine ⟨13422345332523575536814669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8948230221682383691209779 13422345332523575536814669)
    ·
      refine ⟨5033379499696340826305501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13422345332523575536814669 5033379499696340826305501)
      ·
        refine ⟨1887517312386127809864563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5033379499696340826305501 1887517312386127809864563)
        ·
          refine ⟨2831275968579191714796845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1887517312386127809864563 2831275968579191714796845)
          ·
            refine ⟨1061728488217196893048817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2831275968579191714796845 1061728488217196893048817)
            ·
              refine ⟨796296366162897669786613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1061728488217196893048817 796296366162897669786613)
              ·
                refine ⟨74652784327771656542495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 796296366162897669786613 74652784327771656542495)
                ·
                  rfl

theorem cell21_981354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 5].length) (baseStart_981354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_981354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_981354 prefixEnd_981354 := by exact prefixLift 981354
  have htrace : WordTrace (prefixWord ++ tailWord_981354) baseStart_981354 baseEnd_981354 := by
    simpa [prefixWord, tailWord_981354, baseEnd_981354] using wordTrace_append hprefix tailTrace_981354
  have hstable : (prefixWord ++ tailWord_981354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981354).length < 2 ^ (prefixWord ++ tailWord_981354).sum := by decide
  have hdescent : baseEnd_981354 < baseStart_981354 := by decide
  rcases family_descends (prefixWord ++ tailWord_981354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981385 : List Nat := [1, 2, 1, 1, 6, 2, 3, 2, 3]
def baseStart_981385 : Nat := 118140960795 + 981385 * 2 ^ 59
def prefixEnd_981385 : Nat := 4983230072969 + 3 ^ 40 * 981385 * 2
def baseEnd_981385 : Nat := 223965427605665804610755

theorem tailTrace_981385 : CollatzResearch.WordTrace tailWord_981385 prefixEnd_981385 223965427605665804610755 := by
  unfold tailWord_981385
  simp only [CollatzResearch.WordTrace]
  refine ⟨35794051549617227059217609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23862701033078151372811739 35794051549617227059217609)
  ·
    refine ⟨26845538662212920294413207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35794051549617227059217609 26845538662212920294413207)
    ·
      refine ⟨40268307993319380441619811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26845538662212920294413207 40268307993319380441619811)
      ·
        refine ⟨60402461989979070662429717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40268307993319380441619811 60402461989979070662429717)
        ·
          refine ⟨2831365405780268937301393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 60402461989979070662429717 2831365405780268937301393)
          ·
            refine ⟨2123524054335201702976045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2831365405780268937301393 2123524054335201702976045)
            ·
              refine ⟨796321520375700638616017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2123524054335201702976045 796321520375700638616017)
              ·
                refine ⟨597241140281775478962013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 796321520375700638616017 597241140281775478962013)
                ·
                  refine ⟨223965427605665804610755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 597241140281775478962013 223965427605665804610755)
                  ·
                    rfl

theorem cell21_981385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 2, 3].length) (baseStart_981385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_981385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_981385 prefixEnd_981385 := by exact prefixLift 981385
  have htrace : WordTrace (prefixWord ++ tailWord_981385) baseStart_981385 baseEnd_981385 := by
    simpa [prefixWord, tailWord_981385, baseEnd_981385] using wordTrace_append hprefix tailTrace_981385
  have hstable : (prefixWord ++ tailWord_981385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981385).length < 2 ^ (prefixWord ++ tailWord_981385).sum := by decide
  have hdescent : baseEnd_981385 < baseStart_981385 := by decide
  rcases family_descends (prefixWord ++ tailWord_981385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981472 : List Nat := [2, 1, 1, 3, 1, 1, 7, 5]
def baseStart_981472 : Nat := 118140960795 + 981472 * 2 ^ 59
def prefixEnd_981472 : Nat := 4983230072969 + 3 ^ 40 * 981472 * 2
def baseEnd_981472 : Nat := 74661760730324328886859

theorem tailTrace_981472 : CollatzResearch.WordTrace tailWord_981472 prefixEnd_981472 74661760730324328886859 := by
  unfold tailWord_981472
  simp only [CollatzResearch.WordTrace]
  refine ⟨17898612350151020458817335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23864816466868027278423113 17898612350151020458817335)
  ·
    refine ⟨26847918525226530688226003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17898612350151020458817335 26847918525226530688226003)
    ·
      refine ⟨40271877787839796032339005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26847918525226530688226003 40271877787839796032339005)
      ·
        refine ⟨15101954170439923512127127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40271877787839796032339005 15101954170439923512127127)
        ·
          refine ⟨22652931255659885268190691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15101954170439923512127127 22652931255659885268190691)
          ·
            refine ⟨33979396883489827902286037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22652931255659885268190691 33979396883489827902286037)
            ·
              refine ⟨796392114456792841459829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 33979396883489827902286037 796392114456792841459829)
              ·
                refine ⟨74661760730324328886859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 796392114456792841459829 74661760730324328886859)
                ·
                  rfl

theorem cell21_981472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 5].length) (baseStart_981472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_981472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_981472 prefixEnd_981472 := by exact prefixLift 981472
  have htrace : WordTrace (prefixWord ++ tailWord_981472) baseStart_981472 baseEnd_981472 := by
    simpa [prefixWord, tailWord_981472, baseEnd_981472] using wordTrace_append hprefix tailTrace_981472
  have hstable : (prefixWord ++ tailWord_981472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981472).length < 2 ^ (prefixWord ++ tailWord_981472).sum := by decide
  have hdescent : baseEnd_981472 < baseStart_981472 := by decide
  rcases family_descends (prefixWord ++ tailWord_981472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981503 : List Nat := [1, 1, 2, 2, 1, 2, 3, 6, 3]
def baseStart_981503 : Nat := 118140960795 + 981503 * 2 ^ 59
def prefixEnd_981503 : Nat := 4983230072969 + 3 ^ 40 * 981503 * 2
def baseEnd_981503 : Nat := 223992356813323821643847

theorem tailTrace_981503 : CollatzResearch.WordTrace tailWord_981503 prefixEnd_981503 223992356813323821643847 := by
  unfold tailWord_981503
  simp only [CollatzResearch.WordTrace]
  refine ⟨35798355363189733212013163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23865570242126488808008775 35798355363189733212013163)
  ·
    refine ⟨53697533044784599818019745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35798355363189733212013163 53697533044784599818019745)
    ·
      refine ⟨40273149783588449863514809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53697533044784599818019745 40273149783588449863514809)
      ·
        refine ⟨30204862337691337397636107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40273149783588449863514809 30204862337691337397636107)
        ·
          refine ⟨45307293506537006096454161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30204862337691337397636107 45307293506537006096454161)
          ·
            refine ⟨33980470129902754572340621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45307293506537006096454161 33980470129902754572340621)
            ·
              refine ⟨12742676298713532964627733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33980470129902754572340621 12742676298713532964627733)
              ·
                refine ⟨597312951502196857716925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12742676298713532964627733 597312951502196857716925)
                ·
                  refine ⟨223992356813323821643847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 597312951502196857716925 223992356813323821643847)
                  ·
                    rfl

theorem cell21_981503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 6, 3].length) (baseStart_981503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_981503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_981503 prefixEnd_981503 := by exact prefixLift 981503
  have htrace : WordTrace (prefixWord ++ tailWord_981503) baseStart_981503 baseEnd_981503 := by
    simpa [prefixWord, tailWord_981503, baseEnd_981503] using wordTrace_append hprefix tailTrace_981503
  have hstable : (prefixWord ++ tailWord_981503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981503).length < 2 ^ (prefixWord ++ tailWord_981503).sum := by decide
  have hdescent : baseEnd_981503 < baseStart_981503 := by decide
  rcases family_descends (prefixWord ++ tailWord_981503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981610 : List Nat := [3, 1, 3, 2, 1, 1, 4, 2, 4]
def baseStart_981610 : Nat := 118140960795 + 981610 * 2 ^ 59
def prefixEnd_981610 : Nat := 4983230072969 + 3 ^ 40 * 981610 * 2
def baseEnd_981610 : Nat := 224016775671115413360295

theorem tailTrace_981610 : CollatzResearch.WordTrace tailWord_981610 prefixEnd_981610 224016775671115413360295 := by
  unfold tailWord_981610
  simp only [CollatzResearch.WordTrace]
  refine ⟨8950564493450522621539571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23868171982534726990772189 8950564493450522621539571)
  ·
    refine ⟨13425846740175783932309357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8950564493450522621539571 13425846740175783932309357)
    ·
      refine ⟨5034692527565918974616009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13425846740175783932309357 5034692527565918974616009)
      ·
        refine ⟨3776019395674439230962007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5034692527565918974616009 3776019395674439230962007)
        ·
          refine ⟨5664029093511658846443011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3776019395674439230962007 5664029093511658846443011)
          ·
            refine ⟨8496043640267488269664517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5664029093511658846443011 8496043640267488269664517)
            ·
              refine ⟨1593008182550154050562097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8496043640267488269664517 1593008182550154050562097)
              ·
                refine ⟨1194756136912615537921573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1593008182550154050562097 1194756136912615537921573)
                ·
                  refine ⟨224016775671115413360295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1194756136912615537921573 224016775671115413360295)
                  ·
                    rfl

theorem cell21_981610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2, 4].length) (baseStart_981610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_981610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_981610 prefixEnd_981610 := by exact prefixLift 981610
  have htrace : WordTrace (prefixWord ++ tailWord_981610) baseStart_981610 baseEnd_981610 := by
    simpa [prefixWord, tailWord_981610, baseEnd_981610] using wordTrace_append hprefix tailTrace_981610
  have hstable : (prefixWord ++ tailWord_981610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981610).length < 2 ^ (prefixWord ++ tailWord_981610).sum := by decide
  have hdescent : baseEnd_981610 < baseStart_981610 := by decide
  rcases family_descends (prefixWord ++ tailWord_981610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981613 : List Nat := [1, 5, 1, 1, 3, 1, 4, 2, 3]
def baseStart_981613 : Nat := 118140960795 + 981613 * 2 ^ 59
def prefixEnd_981613 : Nat := 4983230072969 + 3 ^ 40 * 981613 * 2
def baseEnd_981613 : Nat := 224017460311988074810289

theorem tailTrace_981613 : CollatzResearch.WordTrace tailWord_981613 prefixEnd_981613 224017460311988074810289 := by
  unfold tailWord_981613
  simp only [CollatzResearch.WordTrace]
  refine ⟨35802367392791221998517493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23868244928527481332344995 35802367392791221998517493)
  ·
    refine ⟨3356471943074177062361015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35802367392791221998517493 3356471943074177062361015)
    ·
      refine ⟨5034707914611265593541523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3356471943074177062361015 5034707914611265593541523)
      ·
        refine ⟨7552061871916898390312285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5034707914611265593541523 7552061871916898390312285)
        ·
          refine ⟨2832023201968836896367107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7552061871916898390312285 2832023201968836896367107)
          ·
            refine ⟨4248034802953255344550661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2832023201968836896367107 4248034802953255344550661)
            ·
              refine ⟨796506525553735377103249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4248034802953255344550661 796506525553735377103249)
              ·
                refine ⟨597379894165301532827437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 796506525553735377103249 597379894165301532827437)
                ·
                  refine ⟨224017460311988074810289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 597379894165301532827437 224017460311988074810289)
                  ·
                    rfl

theorem cell21_981613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_981613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_981613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_981613 prefixEnd_981613 := by exact prefixLift 981613
  have htrace : WordTrace (prefixWord ++ tailWord_981613) baseStart_981613 baseEnd_981613 := by
    simpa [prefixWord, tailWord_981613, baseEnd_981613] using wordTrace_append hprefix tailTrace_981613
  have hstable : (prefixWord ++ tailWord_981613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981613).length < 2 ^ (prefixWord ++ tailWord_981613).sum := by decide
  have hdescent : baseEnd_981613 < baseStart_981613 := by decide
  rcases family_descends (prefixWord ++ tailWord_981613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981700 : List Nat := [2, 3, 3, 1, 1, 3, 1, 7]
def baseStart_981700 : Nat := 118140960795 + 981700 * 2 ^ 59
def prefixEnd_981700 : Nat := 4983230072969 + 3 ^ 40 * 981700 * 2
def baseEnd_981700 : Nat := 74679104965765085620037

theorem tailTrace_981700 : CollatzResearch.WordTrace tailWord_981700 prefixEnd_981700 74679104965765085620037 := by
  unfold tailWord_981700
  simp only [CollatzResearch.WordTrace]
  refine ⟨17902770271738017928467277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23870360362317357237956369 17902770271738017928467277)
  ·
    refine ⟨6713538851901756723175229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17902770271738017928467277 6713538851901756723175229)
    ·
      refine ⟨2517577069463158771190711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6713538851901756723175229 2517577069463158771190711)
      ·
        refine ⟨3776365604194738156786067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2517577069463158771190711 3776365604194738156786067)
        ·
          refine ⟨5664548406292107235179101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3776365604194738156786067 5664548406292107235179101)
          ·
            refine ⟨2124205652359540213192163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5664548406292107235179101 2124205652359540213192163)
            ·
              refine ⟨3186308478539310319788245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2124205652359540213192163 3186308478539310319788245)
              ·
                refine ⟨74679104965765085620037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3186308478539310319788245 74679104965765085620037)
                ·
                  rfl

theorem cell21_981700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 7].length) (baseStart_981700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_981700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_981700 prefixEnd_981700 := by exact prefixLift 981700
  have htrace : WordTrace (prefixWord ++ tailWord_981700) baseStart_981700 baseEnd_981700 := by
    simpa [prefixWord, tailWord_981700, baseEnd_981700] using wordTrace_append hprefix tailTrace_981700
  have hstable : (prefixWord ++ tailWord_981700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981700).length < 2 ^ (prefixWord ++ tailWord_981700).sum := by decide
  have hdescent : baseEnd_981700 < baseStart_981700 := by decide
  rcases family_descends (prefixWord ++ tailWord_981700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981717 : List Nat := [1, 3, 2, 5, 1, 2, 7]
def baseStart_981717 : Nat := 118140960795 + 981717 * 2 ^ 59
def prefixEnd_981717 : Nat := 4983230072969 + 3 ^ 40 * 981717 * 2
def baseEnd_981717 : Nat := 24893466058767445008527

theorem tailTrace_981717 : CollatzResearch.WordTrace tailWord_981717 prefixEnd_981717 24893466058767445008527 := by
  unfold tailWord_981717
  simp only [CollatzResearch.WordTrace]
  refine ⟨35806160584414447760303405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23870773722942965173535603 35806160584414447760303405)
  ·
    refine ⟨13427310219155417910113777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35806160584414447760303405 13427310219155417910113777)
    ·
      refine ⟨10070482664366563432585333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13427310219155417910113777 10070482664366563432585333)
      ·
        refine ⟨944107749784365321804875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10070482664366563432585333 944107749784365321804875)
        ·
          refine ⟨1416161624676547982707313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 944107749784365321804875 1416161624676547982707313)
          ·
            refine ⟨1062121218507410987030485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1416161624676547982707313 1062121218507410987030485)
            ·
              refine ⟨24893466058767445008527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1062121218507410987030485 24893466058767445008527)
              ·
                rfl

theorem cell21_981717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 7].length) (baseStart_981717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_981717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_981717 prefixEnd_981717 := by exact prefixLift 981717
  have htrace : WordTrace (prefixWord ++ tailWord_981717) baseStart_981717 baseEnd_981717 := by
    simpa [prefixWord, tailWord_981717, baseEnd_981717] using wordTrace_append hprefix tailTrace_981717
  have hstable : (prefixWord ++ tailWord_981717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981717).length < 2 ^ (prefixWord ++ tailWord_981717).sum := by decide
  have hdescent : baseEnd_981717 < baseStart_981717 := by decide
  rcases family_descends (prefixWord ++ tailWord_981717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981731 : List Nat := [1, 1, 1, 7, 1, 1, 3, 1, 5]
def baseStart_981731 : Nat := 118140960795 + 981731 * 2 ^ 59
def prefixEnd_981731 : Nat := 4983230072969 + 3 ^ 40 * 981731 * 2
def baseEnd_981731 : Nat := 224044389519646091843381

theorem tailTrace_981731 : CollatzResearch.WordTrace tailWord_981731 prefixEnd_981731 224044389519646091843381 := by
  unfold tailWord_981731
  simp only [CollatzResearch.WordTrace]
  refine ⟨35806671206363728151313047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23871114137575818767542031 35806671206363728151313047)
  ·
    refine ⟨53710006809545592226969571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35806671206363728151313047 53710006809545592226969571)
    ·
      refine ⟨80565010214318388340454357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53710006809545592226969571 80565010214318388340454357)
      ·
        refine ⟨1888242426898087226729399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 80565010214318388340454357 1888242426898087226729399)
        ·
          refine ⟨2832363640347130840094099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1888242426898087226729399 2832363640347130840094099)
          ·
            refine ⟨4248545460520696260141149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2832363640347130840094099 4248545460520696260141149)
            ·
              refine ⟨1593204547695261097552931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4248545460520696260141149 1593204547695261097552931)
              ·
                refine ⟨2389806821542891646329397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1593204547695261097552931 2389806821542891646329397)
                ·
                  refine ⟨224044389519646091843381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2389806821542891646329397 224044389519646091843381)
                  ·
                    rfl

theorem cell21_981731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 5].length) (baseStart_981731 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_981731 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_981731 prefixEnd_981731 := by exact prefixLift 981731
  have htrace : WordTrace (prefixWord ++ tailWord_981731) baseStart_981731 baseEnd_981731 := by
    simpa [prefixWord, tailWord_981731, baseEnd_981731] using wordTrace_append hprefix tailTrace_981731
  have hstable : (prefixWord ++ tailWord_981731).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981731).length < 2 ^ (prefixWord ++ tailWord_981731).sum := by decide
  have hdescent : baseEnd_981731 < baseStart_981731 := by decide
  rcases family_descends (prefixWord ++ tailWord_981731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981745 : List Nat := [1, 2, 2, 2, 2, 2, 3, 3, 4]
def baseStart_981745 : Nat := 118140960795 + 981745 * 2 ^ 59
def prefixEnd_981745 : Nat := 4983230072969 + 3 ^ 40 * 981745 * 2
def baseEnd_981745 : Nat := 224047584510385178610019

theorem tailTrace_981745 : CollatzResearch.WordTrace tailWord_981745 prefixEnd_981745 224047584510385178610019 := by
  unfold tailWord_981745
  simp only [CollatzResearch.WordTrace]
  refine ⟨35807181828313008542322689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23871454552208672361548459 35807181828313008542322689)
  ·
    refine ⟨26855386371234756406742017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35807181828313008542322689 26855386371234756406742017)
    ·
      refine ⟨20141539778426067305056513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26855386371234756406742017 20141539778426067305056513)
      ·
        refine ⟨15106154833819550478792385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20141539778426067305056513 15106154833819550478792385)
        ·
          refine ⟨11329616125364662859094289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15106154833819550478792385 11329616125364662859094289)
          ·
            refine ⟨8497212094023497144320717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11329616125364662859094289 8497212094023497144320717)
            ·
              refine ⟨3186454535258811429120269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8497212094023497144320717 3186454535258811429120269)
              ·
                refine ⟨1194920450722054285920101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3186454535258811429120269 1194920450722054285920101)
                ·
                  refine ⟨224047584510385178610019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1194920450722054285920101 224047584510385178610019)
                  ·
                    rfl

theorem cell21_981745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 4].length) (baseStart_981745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_981745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_981745 prefixEnd_981745 := by exact prefixLift 981745
  have htrace : WordTrace (prefixWord ++ tailWord_981745) baseStart_981745 baseEnd_981745 := by
    simpa [prefixWord, tailWord_981745, baseEnd_981745] using wordTrace_append hprefix tailTrace_981745
  have hstable : (prefixWord ++ tailWord_981745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981745).length < 2 ^ (prefixWord ++ tailWord_981745).sum := by decide
  have hdescent : baseEnd_981745 < baseStart_981745 := by decide
  rcases family_descends (prefixWord ++ tailWord_981745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981883 : List Nat := [1, 1, 1, 1, 1, 5, 5, 3, 3]
def baseStart_981883 : Nat := 118140960795 + 981883 * 2 ^ 59
def prefixEnd_981883 : Nat := 4983230072969 + 3 ^ 40 * 981883 * 2
def baseEnd_981883 : Nat := 224079077990527605309737

theorem tailTrace_981883 : CollatzResearch.WordTrace tailWord_981883 prefixEnd_981883 224079077990527605309737 := by
  unfold tailWord_981883
  simp only [CollatzResearch.WordTrace]
  refine ⟨35812215101813058110846303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23874810067875372073897535 35812215101813058110846303)
  ·
    refine ⟨53718322652719587166269455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35812215101813058110846303 53718322652719587166269455)
    ·
      refine ⟨80577483979079380749404183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53718322652719587166269455 80577483979079380749404183)
      ·
        refine ⟨120866225968619071124106275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80577483979079380749404183 120866225968619071124106275)
        ·
          refine ⟨181299338952928606686159413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120866225968619071124106275 181299338952928606686159413)
          ·
            refine ⟨16996813026837056876827445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 181299338952928606686159413 16996813026837056876827445)
            ·
              refine ⟨1593451221265974082202573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16996813026837056876827445 1593451221265974082202573)
              ·
                refine ⟨597544207974740280825965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1593451221265974082202573 597544207974740280825965)
                ·
                  refine ⟨224079077990527605309737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 597544207974740280825965 224079077990527605309737)
                  ·
                    rfl

theorem cell21_981883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 3, 3].length) (baseStart_981883 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_981883 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_981883 prefixEnd_981883 := by exact prefixLift 981883
  have htrace : WordTrace (prefixWord ++ tailWord_981883) baseStart_981883 baseEnd_981883 := by
    simpa [prefixWord, tailWord_981883, baseEnd_981883] using wordTrace_append hprefix tailTrace_981883
  have hstable : (prefixWord ++ tailWord_981883).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981883).length < 2 ^ (prefixWord ++ tailWord_981883).sum := by decide
  have hdescent : baseEnd_981883 < baseStart_981883 := by decide
  rcases family_descends (prefixWord ++ tailWord_981883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981886 : List Nat := [4, 2, 3, 1, 3, 1, 7]
def baseStart_981886 : Nat := 118140960795 + 981886 * 2 ^ 59
def prefixEnd_981886 : Nat := 4983230072969 + 3 ^ 40 * 981886 * 2
def baseEnd_981886 : Nat := 24897751403488918528859

theorem tailTrace_981886 : CollatzResearch.WordTrace tailWord_981886 prefixEnd_981886 24897751403488918528859 := by
  unfold tailWord_981886
  simp only [CollatzResearch.WordTrace]
  refine ⟨4476540565100273702900689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23874883013868126415470341 4476540565100273702900689)
  ·
    refine ⟨3357405423825205277175517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4476540565100273702900689 3357405423825205277175517)
    ·
      refine ⟨1259027033934451978940819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3357405423825205277175517 1259027033934451978940819)
      ·
        refine ⟨1888540550901677968411229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1259027033934451978940819 1888540550901677968411229)
        ·
          refine ⟨708202706588129238154211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1888540550901677968411229 708202706588129238154211)
          ·
            refine ⟨1062304059882193857231317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708202706588129238154211 1062304059882193857231317)
            ·
              refine ⟨24897751403488918528859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1062304059882193857231317 24897751403488918528859)
              ·
                rfl

theorem cell21_981886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 7].length) (baseStart_981886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_981886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_981886 prefixEnd_981886 := by exact prefixLift 981886
  have htrace : WordTrace (prefixWord ++ tailWord_981886) baseStart_981886 baseEnd_981886 := by
    simpa [prefixWord, tailWord_981886, baseEnd_981886] using wordTrace_append hprefix tailTrace_981886
  have hstable : (prefixWord ++ tailWord_981886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981886).length < 2 ^ (prefixWord ++ tailWord_981886).sum := by decide
  have hdescent : baseEnd_981886 < baseStart_981886 := by decide
  rcases family_descends (prefixWord ++ tailWord_981886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981911 : List Nat := [1, 1, 3, 3, 1, 2, 4, 6]
def baseStart_981911 : Nat := 118140960795 + 981911 * 2 ^ 59
def prefixEnd_981911 : Nat := 4983230072969 + 3 ^ 40 * 981911 * 2
def baseEnd_981911 : Nat := 74695155990668592947671

theorem tailTrace_981911 : CollatzResearch.WordTrace tailWord_981911 prefixEnd_981911 74695155990668592947671 := by
  unfold tailWord_981911
  simp only [CollatzResearch.WordTrace]
  refine ⟨35813236345711618892865587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23875490897141079261910391 35813236345711618892865587)
  ·
    refine ⟨53719854518567428339298381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35813236345711618892865587 53719854518567428339298381)
    ·
      refine ⟨20144945444462785627236893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53719854518567428339298381 20144945444462785627236893)
      ·
        refine ⟨7554354541673544610213835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20144945444462785627236893 7554354541673544610213835)
        ·
          refine ⟨11331531812510316915320753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7554354541673544610213835 11331531812510316915320753)
          ·
            refine ⟨8498648859382737686490565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11331531812510316915320753 8498648859382737686490565)
            ·
              refine ⟨1593496661134263316216981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8498648859382737686490565 1593496661134263316216981)
              ·
                refine ⟨74695155990668592947671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1593496661134263316216981 74695155990668592947671)
                ·
                  rfl

theorem cell21_981911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 6].length) (baseStart_981911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_981911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_981911 prefixEnd_981911 := by exact prefixLift 981911
  have htrace : WordTrace (prefixWord ++ tailWord_981911) baseStart_981911 baseEnd_981911 := by
    simpa [prefixWord, tailWord_981911, baseEnd_981911] using wordTrace_append hprefix tailTrace_981911
  have hstable : (prefixWord ++ tailWord_981911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981911).length < 2 ^ (prefixWord ++ tailWord_981911).sum := by decide
  have hdescent : baseEnd_981911 < baseStart_981911 := by decide
  rcases family_descends (prefixWord ++ tailWord_981911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981914 : List Nat := [3, 1, 1, 4, 3, 1, 1, 3, 4]
def baseStart_981914 : Nat := 118140960795 + 981914 * 2 ^ 59
def prefixEnd_981914 : Nat := 4983230072969 + 3 ^ 40 * 981914 * 2
def baseEnd_981914 : Nat := 224086152612878440293007

theorem tailTrace_981914 : CollatzResearch.WordTrace tailWord_981914 prefixEnd_981914 224086152612878440293007 := by
  unfold tailWord_981914
  simp only [CollatzResearch.WordTrace]
  refine ⟨8953336441175187601306199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23875563843133833603483197 8953336441175187601306199)
  ·
    refine ⟨13430004661762781401959299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8953336441175187601306199 13430004661762781401959299)
    ·
      refine ⟨20145006992644172102938949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13430004661762781401959299 20145006992644172102938949)
      ·
        refine ⟨3777188811120782269301053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20145006992644172102938949 3777188811120782269301053)
        ·
          refine ⟨1416445804170293350987895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3777188811120782269301053 1416445804170293350987895)
          ·
            refine ⟨2124668706255440026481843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1416445804170293350987895 2124668706255440026481843)
            ·
              refine ⟨3187003059383160039722765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2124668706255440026481843 3187003059383160039722765)
              ·
                refine ⟨1195126147268685014896037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3187003059383160039722765 1195126147268685014896037)
                ·
                  refine ⟨224086152612878440293007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1195126147268685014896037 224086152612878440293007)
                  ·
                    rfl

theorem cell21_981914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3, 4].length) (baseStart_981914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_981914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_981914 prefixEnd_981914 := by exact prefixLift 981914
  have htrace : WordTrace (prefixWord ++ tailWord_981914) baseStart_981914 baseEnd_981914 := by
    simpa [prefixWord, tailWord_981914, baseEnd_981914] using wordTrace_append hprefix tailTrace_981914
  have hstable : (prefixWord ++ tailWord_981914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981914).length < 2 ^ (prefixWord ++ tailWord_981914).sum := by decide
  have hdescent : baseEnd_981914 < baseStart_981914 := by decide
  rcases family_descends (prefixWord ++ tailWord_981914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982052 : List Nat := [2, 3, 1, 4, 1, 1, 3, 3, 3]
def baseStart_982052 : Nat := 118140960795 + 982052 * 2 ^ 59
def prefixEnd_982052 : Nat := 4983230072969 + 3 ^ 40 * 982052 * 2
def baseEnd_982052 : Nat := 224117646093020866992725

theorem tailTrace_982052 : CollatzResearch.WordTrace tailWord_982052 prefixEnd_982052 224117646093020866992725 := by
  unfold tailWord_982052
  simp only [CollatzResearch.WordTrace]
  refine ⟨17909189519100399986874205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23878919358800533315832273 17909189519100399986874205)
  ·
    refine ⟨6715946069662649995077827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17909189519100399986874205 6715946069662649995077827)
    ·
      refine ⟨10073919104493974992616741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6715946069662649995077827 10073919104493974992616741)
      ·
        refine ⟨1888859832092620311115639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10073919104493974992616741 1888859832092620311115639)
        ·
          refine ⟨2833289748138930466673459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1888859832092620311115639 2833289748138930466673459)
          ·
            refine ⟨4249934622208395700010189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2833289748138930466673459 4249934622208395700010189)
            ·
              refine ⟨1593725483328148387503821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4249934622208395700010189 1593725483328148387503821)
              ·
                refine ⟨597647056248055645313933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1593725483328148387503821 597647056248055645313933)
                ·
                  refine ⟨224117646093020866992725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 597647056248055645313933 224117646093020866992725)
                  ·
                    rfl

theorem cell21_982052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 3, 3].length) (baseStart_982052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_982052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_982052 prefixEnd_982052 := by exact prefixLift 982052
  have htrace : WordTrace (prefixWord ++ tailWord_982052) baseStart_982052 baseEnd_982052 := by
    simpa [prefixWord, tailWord_982052, baseEnd_982052] using wordTrace_append hprefix tailTrace_982052
  have hstable : (prefixWord ++ tailWord_982052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982052).length < 2 ^ (prefixWord ++ tailWord_982052).sum := by decide
  have hdescent : baseEnd_982052 < baseStart_982052 := by decide
  rcases family_descends (prefixWord ++ tailWord_982052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982125 : List Nat := [1, 5, 1, 1, 2, 2, 1, 4, 4]
def baseStart_982125 : Nat := 118140960795 + 982125 * 2 ^ 59
def prefixEnd_982125 : Nat := 4983230072969 + 3 ^ 40 * 982125 * 2
def baseEnd_982125 : Nat := 224134305687588962275909

theorem tailTrace_982125 : CollatzResearch.WordTrace tailWord_982125 prefixEnd_982125 224134305687588962275909 := by
  unfold tailWord_982125
  simp only [CollatzResearch.WordTrace]
  refine ⟨35821041566936333441155829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23880694377957555627437219 35821041566936333441155829)
  ·
    refine ⟨3358222646900281260108359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35821041566936333441155829 3358222646900281260108359)
    ·
      refine ⟨5037333970350421890162539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3358222646900281260108359 5037333970350421890162539)
      ·
        refine ⟨7556000955525632835243809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5037333970350421890162539 7556000955525632835243809)
        ·
          refine ⟨5667000716644224626432857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7556000955525632835243809 5667000716644224626432857)
          ·
            refine ⟨4250250537483168469824643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5667000716644224626432857 4250250537483168469824643)
            ·
              refine ⟨6375375806224752704736965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4250250537483168469824643 6375375806224752704736965)
              ·
                refine ⟨1195382963667141132138181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6375375806224752704736965 1195382963667141132138181)
                ·
                  refine ⟨224134305687588962275909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1195382963667141132138181 224134305687588962275909)
                  ·
                    rfl

theorem cell21_982125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_982125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_982125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_982125 prefixEnd_982125 := by exact prefixLift 982125
  have htrace : WordTrace (prefixWord ++ tailWord_982125) baseStart_982125 baseEnd_982125 := by
    simpa [prefixWord, tailWord_982125, baseEnd_982125] using wordTrace_append hprefix tailTrace_982125
  have hstable : (prefixWord ++ tailWord_982125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982125).length < 2 ^ (prefixWord ++ tailWord_982125).sum := by decide
  have hdescent : baseEnd_982125 < baseStart_982125 := by decide
  rcases family_descends (prefixWord ++ tailWord_982125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982153 : List Nat := [1, 2, 1, 1, 4, 3, 1, 1, 7]
def baseStart_982153 : Nat := 118140960795 + 982153 * 2 ^ 59
def prefixEnd_982153 : Nat := 4983230072969 + 3 ^ 40 * 982153 * 2
def baseEnd_982153 : Nat := 224140695669067135809185

theorem tailTrace_982153 : CollatzResearch.WordTrace tailWord_982153 prefixEnd_982153 224140695669067135809185 := by
  unfold tailWord_982153
  simp only [CollatzResearch.WordTrace]
  refine ⟨35822062810834894223175113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23881375207223262815450075 35822062810834894223175113)
  ·
    refine ⟨26866547108126170667381335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35822062810834894223175113 26866547108126170667381335)
    ·
      refine ⟨40299820662189256001072003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26866547108126170667381335 40299820662189256001072003)
      ·
        refine ⟨60449730993283884001608005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40299820662189256001072003 60449730993283884001608005)
        ·
          refine ⟨11334324561240728250301501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60449730993283884001608005 11334324561240728250301501)
          ·
            refine ⟨4250371710465273093863063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11334324561240728250301501 4250371710465273093863063)
            ·
              refine ⟨6375557565697909640794595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4250371710465273093863063 6375557565697909640794595)
              ·
                refine ⟨9563336348546864461191893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6375557565697909640794595 9563336348546864461191893)
                ·
                  refine ⟨224140695669067135809185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9563336348546864461191893 224140695669067135809185)
                  ·
                    rfl

theorem cell21_982153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 7].length) (baseStart_982153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_982153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_982153 prefixEnd_982153 := by exact prefixLift 982153
  have htrace : WordTrace (prefixWord ++ tailWord_982153) baseStart_982153 baseEnd_982153 := by
    simpa [prefixWord, tailWord_982153, baseEnd_982153] using wordTrace_append hprefix tailTrace_982153
  have hstable : (prefixWord ++ tailWord_982153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982153).length < 2 ^ (prefixWord ++ tailWord_982153).sum := by decide
  have hdescent : baseEnd_982153 < baseStart_982153 := by decide
  rcases family_descends (prefixWord ++ tailWord_982153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982232 : List Nat := [2, 1, 2, 2, 6, 1, 7]
def baseStart_982232 : Nat := 118140960795 + 982232 * 2 ^ 59
def prefixEnd_982232 : Nat := 4983230072969 + 3 ^ 40 * 982232 * 2
def baseEnd_982232 : Nat := 24906524949486728221373

theorem tailTrace_982232 : CollatzResearch.WordTrace tailWord_982232 prefixEnd_982232 24906524949486728221373 := by
  unfold tailWord_982232
  simp only [CollatzResearch.WordTrace]
  refine ⟨17912472088774345357650475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23883296118365793810200633 17912472088774345357650475)
  ·
    refine ⟨26868708133161518036475713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17912472088774345357650475 26868708133161518036475713)
    ·
      refine ⟨20151531099871138527356785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26868708133161518036475713 20151531099871138527356785)
      ·
        refine ⟨15113648324903353895517589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20151531099871138527356785 15113648324903353895517589)
        ·
          refine ⟨708452265229844713852387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15113648324903353895517589 708452265229844713852387)
          ·
            refine ⟨1062678397844767070778581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708452265229844713852387 1062678397844767070778581)
            ·
              refine ⟨24906524949486728221373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1062678397844767070778581 24906524949486728221373)
              ·
                rfl

theorem cell21_982232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 7].length) (baseStart_982232 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_982232 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_982232 prefixEnd_982232 := by exact prefixLift 982232
  have htrace : WordTrace (prefixWord ++ tailWord_982232) baseStart_982232 baseEnd_982232 := by
    simpa [prefixWord, tailWord_982232, baseEnd_982232] using wordTrace_append hprefix tailTrace_982232
  have hstable : (prefixWord ++ tailWord_982232).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982232).length < 2 ^ (prefixWord ++ tailWord_982232).sum := by decide
  have hdescent : baseEnd_982232 < baseStart_982232 := by decide
  rcases family_descends (prefixWord ++ tailWord_982232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982305 : List Nat := [1, 2, 3, 2, 1, 1, 1, 5, 5]
def baseStart_982305 : Nat := 118140960795 + 982305 * 2 ^ 59
def prefixEnd_982305 : Nat := 4983230072969 + 3 ^ 40 * 982305 * 2
def baseEnd_982305 : Nat := 224175384139948649275541

theorem tailTrace_982305 : CollatzResearch.WordTrace tailWord_982305 prefixEnd_982305 224175384139948649275541 := by
  unfold tailWord_982305
  simp only [CollatzResearch.WordTrace]
  refine ⟨35827606706284224182708369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23885071137522816121805579 35827606706284224182708369)
  ·
    refine ⟨26870705029713168137031277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35827606706284224182708369 26870705029713168137031277)
    ·
      refine ⟨10076514386142438051386729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26870705029713168137031277 10076514386142438051386729)
      ·
        refine ⟨7557385789606828538540047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10076514386142438051386729 7557385789606828538540047)
        ·
          refine ⟨11336078684410242807810071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7557385789606828538540047 11336078684410242807810071)
          ·
            refine ⟨17004118026615364211715107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11336078684410242807810071 17004118026615364211715107)
            ·
              refine ⟨25506177039923046317572661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17004118026615364211715107 25506177039923046317572661)
              ·
                refine ⟨2391204097492785592272437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25506177039923046317572661 2391204097492785592272437)
                ·
                  refine ⟨224175384139948649275541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2391204097492785592272437 224175384139948649275541)
                  ·
                    rfl

theorem cell21_982305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 5].length) (baseStart_982305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_982305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_982305 prefixEnd_982305 := by exact prefixLift 982305
  have htrace : WordTrace (prefixWord ++ tailWord_982305) baseStart_982305 baseEnd_982305 := by
    simpa [prefixWord, tailWord_982305, baseEnd_982305] using wordTrace_append hprefix tailTrace_982305
  have hstable : (prefixWord ++ tailWord_982305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982305).length < 2 ^ (prefixWord ++ tailWord_982305).sum := by decide
  have hdescent : baseEnd_982305 < baseStart_982305 := by decide
  rcases family_descends (prefixWord ++ tailWord_982305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982319 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 8]
def baseStart_982319 : Nat := 118140960795 + 982319 * 2 ^ 59
def prefixEnd_982319 : Nat := 4983230072969 + 3 ^ 40 * 982319 * 2
def baseEnd_982319 : Nat := 224178579130687736042179

theorem tailTrace_982319 : CollatzResearch.WordTrace tailWord_982319 prefixEnd_982319 224178579130687736042179 := by
  unfold tailWord_982319
  simp only [CollatzResearch.WordTrace]
  refine ⟨35828117328233504573718011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23885411552155669715812007 35828117328233504573718011)
  ·
    refine ⟨53742175992350256860577017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35828117328233504573718011 53742175992350256860577017)
    ·
      refine ⟨40306631994262692645432763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53742175992350256860577017 40306631994262692645432763)
      ·
        refine ⟨60459947991394038968149145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40306631994262692645432763 60459947991394038968149145)
        ·
          refine ⟨45344960993545529226111859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60459947991394038968149145 45344960993545529226111859)
          ·
            refine ⟨68017441490318293839167789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45344960993545529226111859 68017441490318293839167789)
            ·
              refine ⟨25506540558869360189687921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68017441490318293839167789 25506540558869360189687921)
              ·
                refine ⟨19129905419152020142265941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25506540558869360189687921 19129905419152020142265941)
                ·
                  refine ⟨224178579130687736042179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19129905419152020142265941 224178579130687736042179)
                  ·
                    rfl

theorem cell21_982319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 8].length) (baseStart_982319 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_982319 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_982319 prefixEnd_982319 := by exact prefixLift 982319
  have htrace : WordTrace (prefixWord ++ tailWord_982319) baseStart_982319 baseEnd_982319 := by
    simpa [prefixWord, tailWord_982319, baseEnd_982319] using wordTrace_append hprefix tailTrace_982319
  have hstable : (prefixWord ++ tailWord_982319).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982319).length < 2 ^ (prefixWord ++ tailWord_982319).sum := by decide
  have hdescent : baseEnd_982319 < baseStart_982319 := by decide
  rcases family_descends (prefixWord ++ tailWord_982319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982322 : List Nat := [3, 2, 1, 1, 4, 2, 1, 2, 5]
def baseStart_982322 : Nat := 118140960795 + 982322 * 2 ^ 59
def prefixEnd_982322 : Nat := 4983230072969 + 3 ^ 40 * 982322 * 2
def baseEnd_982322 : Nat := 224179263771560397492173

theorem tailTrace_982322 : CollatzResearch.WordTrace tailWord_982322 prefixEnd_982322 224179263771560397492173 := by
  unfold tailWord_982322
  simp only [CollatzResearch.WordTrace]
  refine ⟨8957056686805659021519305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23885484498148424057384813 8957056686805659021519305)
  ·
    refine ⟨6717792515104244266139479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8957056686805659021519305 6717792515104244266139479)
    ·
      refine ⟨10076688772656366399209219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6717792515104244266139479 10076688772656366399209219)
      ·
        refine ⟨15115033158984549598813829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10076688772656366399209219 15115033158984549598813829)
        ·
          refine ⟨2834068717309603049777593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15115033158984549598813829 2834068717309603049777593)
          ·
            refine ⟨2125551537982202287333195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2834068717309603049777593 2125551537982202287333195)
            ·
              refine ⟨3188327306973303430999793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2125551537982202287333195 3188327306973303430999793)
              ·
                refine ⟨2391245480229977573249845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3188327306973303430999793 2391245480229977573249845)
                ·
                  refine ⟨224179263771560397492173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2391245480229977573249845 224179263771560397492173)
                  ·
                    rfl

theorem cell21_982322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_982322 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_982322 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_982322 prefixEnd_982322 := by exact prefixLift 982322
  have htrace : WordTrace (prefixWord ++ tailWord_982322) baseStart_982322 baseEnd_982322 := by
    simpa [prefixWord, tailWord_982322, baseEnd_982322] using wordTrace_append hprefix tailTrace_982322
  have hstable : (prefixWord ++ tailWord_982322).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982322).length < 2 ^ (prefixWord ++ tailWord_982322).sum := by decide
  have hdescent : baseEnd_982322 < baseStart_982322 := by decide
  rcases family_descends (prefixWord ++ tailWord_982322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982350 : List Nat := [4, 1, 1, 1, 1, 1, 12]
def baseStart_982350 : Nat := 118140960795 + 982350 * 2 ^ 59
def prefixEnd_982350 : Nat := 4983230072969 + 3 ^ 40 * 982350 * 2
def baseEnd_982350 : Nat := 24909517083670952336161

theorem tailTrace_982350 : CollatzResearch.WordTrace tailWord_982350 prefixEnd_982350 24909517083670952336161 := by
  unfold tailWord_982350
  simp only [CollatzResearch.WordTrace]
  refine ⟨4478655998890149608512063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23886165327414131245397669 4478655998890149608512063)
  ·
    refine ⟨6717983998335224412768095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4478655998890149608512063 6717983998335224412768095)
    ·
      refine ⟨10076975997502836619152143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6717983998335224412768095 10076975997502836619152143)
      ·
        refine ⟨15115463996254254928728215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10076975997502836619152143 15115463996254254928728215)
        ·
          refine ⟨22673195994381382393092323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15115463996254254928728215 22673195994381382393092323)
          ·
            refine ⟨34009793991572073589638485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22673195994381382393092323 34009793991572073589638485)
            ·
              refine ⟨24909517083670952336161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 34009793991572073589638485 24909517083670952336161)
              ·
                rfl

theorem cell21_982350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 12].length) (baseStart_982350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_982350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_982350 prefixEnd_982350 := by exact prefixLift 982350
  have htrace : WordTrace (prefixWord ++ tailWord_982350) baseStart_982350 baseEnd_982350 := by
    simpa [prefixWord, tailWord_982350, baseEnd_982350] using wordTrace_append hprefix tailTrace_982350
  have hstable : (prefixWord ++ tailWord_982350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982350).length < 2 ^ (prefixWord ++ tailWord_982350).sum := by decide
  have hdescent : baseEnd_982350 < baseStart_982350 := by decide
  rcases family_descends (prefixWord ++ tailWord_982350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982370 : List Nat := [3, 3, 2, 1, 1, 1, 5, 1, 4]
def baseStart_982370 : Nat := 118140960795 + 982370 * 2 ^ 59
def prefixEnd_982370 : Nat := 4983230072969 + 3 ^ 40 * 982370 * 2
def baseEnd_982370 : Nat := 224190218025522980692075

theorem tailTrace_982370 : CollatzResearch.WordTrace tailWord_982370 prefixEnd_982370 224190218025522980692075 := by
  unfold tailWord_982370
  simp only [CollatzResearch.WordTrace]
  refine ⟨8957494362762185070956141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23886651634032493522549709 8957494362762185070956141)
  ·
    refine ⟨3359060386035819401608553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8957494362762185070956141 3359060386035819401608553)
    ·
      refine ⟨2519295289526864551206415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3359060386035819401608553 2519295289526864551206415)
      ·
        refine ⟨3778942934290296826809623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2519295289526864551206415 3778942934290296826809623)
        ·
          refine ⟨5668414401435445240214435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3778942934290296826809623 5668414401435445240214435)
          ·
            refine ⟨8502621602153167860321653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5668414401435445240214435 8502621602153167860321653)
            ·
              refine ⟨797120775201859486905155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8502621602153167860321653 797120775201859486905155)
              ·
                refine ⟨1195681162802789230357733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 797120775201859486905155 1195681162802789230357733)
                ·
                  refine ⟨224190218025522980692075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1195681162802789230357733 224190218025522980692075)
                  ·
                    rfl

theorem cell21_982370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_982370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_982370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_982370 prefixEnd_982370 := by exact prefixLift 982370
  have htrace : WordTrace (prefixWord ++ tailWord_982370) baseStart_982370 baseEnd_982370 := by
    simpa [prefixWord, tailWord_982370, baseEnd_982370] using wordTrace_append hprefix tailTrace_982370
  have hstable : (prefixWord ++ tailWord_982370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982370).length < 2 ^ (prefixWord ++ tailWord_982370).sum := by decide
  have hdescent : baseEnd_982370 < baseStart_982370 := by decide
  rcases family_descends (prefixWord ++ tailWord_982370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982395 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 8]
def baseStart_982395 : Nat := 118140960795 + 982395 * 2 ^ 59
def prefixEnd_982395 : Nat := 4983230072969 + 3 ^ 40 * 982395 * 2
def baseEnd_982395 : Nat := 224195923366128492775357

theorem tailTrace_982395 : CollatzResearch.WordTrace tailWord_982395 prefixEnd_982395 224195923366128492775357 := by
  unfold tailWord_982395
  simp only [CollatzResearch.WordTrace]
  refine ⟨35830889275958169553484639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23887259517305446368989759 35830889275958169553484639)
  ·
    refine ⟨53746333913937254330226959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35830889275958169553484639 53746333913937254330226959)
    ·
      refine ⟨80619500870905881495340439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53746333913937254330226959 80619500870905881495340439)
      ·
        refine ⟨120929251306358822243010659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80619500870905881495340439 120929251306358822243010659)
        ·
          refine ⟨181393876959538233364515989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120929251306358822243010659 181393876959538233364515989)
          ·
            refine ⟨8502837982478354688961687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 181393876959538233364515989 8502837982478354688961687)
            ·
              refine ⟨12754256973717532033442531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8502837982478354688961687 12754256973717532033442531)
              ·
                refine ⟨19131385460576298050163797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12754256973717532033442531 19131385460576298050163797)
                ·
                  refine ⟨224195923366128492775357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19131385460576298050163797 224195923366128492775357)
                  ·
                    rfl

theorem cell21_982395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 8].length) (baseStart_982395 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_982395 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_982395 prefixEnd_982395 := by exact prefixLift 982395
  have htrace : WordTrace (prefixWord ++ tailWord_982395) baseStart_982395 baseEnd_982395 := by
    simpa [prefixWord, tailWord_982395, baseEnd_982395] using wordTrace_append hprefix tailTrace_982395
  have hstable : (prefixWord ++ tailWord_982395).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982395).length < 2 ^ (prefixWord ++ tailWord_982395).sum := by decide
  have hdescent : baseEnd_982395 < baseStart_982395 := by decide
  rcases family_descends (prefixWord ++ tailWord_982395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982412 : List Nat := [2, 2, 1, 2, 1, 3, 2, 4, 4]
def baseStart_982412 : Nat := 118140960795 + 982412 * 2 ^ 59
def prefixEnd_982412 : Nat := 4983230072969 + 3 ^ 40 * 982412 * 2
def baseEnd_982412 : Nat := 224199802997740240991989

theorem tailTrace_982412 : CollatzResearch.WordTrace tailWord_982412 prefixEnd_982412 224199802997740240991989 := by
  unfold tailWord_982412
  simp only [CollatzResearch.WordTrace]
  refine ⟨17915754658448290728426745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23887672877931054304568993 17915754658448290728426745)
  ·
    refine ⟨13436815993836218046320059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17915754658448290728426745 13436815993836218046320059)
    ·
      refine ⟨20155223990754327069480089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13436815993836218046320059 20155223990754327069480089)
      ·
        refine ⟨15116417993065745302110067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20155223990754327069480089 15116417993065745302110067)
        ·
          refine ⟨22674626989598617953165101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15116417993065745302110067 22674626989598617953165101)
          ·
            refine ⟨8502985121099481732436913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22674626989598617953165101 8502985121099481732436913)
            ·
              refine ⟨6377238840824611299327685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8502985121099481732436913 6377238840824611299327685)
              ·
                refine ⟨1195732282654614618623941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6377238840824611299327685 1195732282654614618623941)
                ·
                  refine ⟨224199802997740240991989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1195732282654614618623941 224199802997740240991989)
                  ·
                    rfl

theorem cell21_982412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4, 4].length) (baseStart_982412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_982412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_982412 prefixEnd_982412 := by exact prefixLift 982412
  have htrace : WordTrace (prefixWord ++ tailWord_982412) baseStart_982412 baseEnd_982412 := by
    simpa [prefixWord, tailWord_982412, baseEnd_982412] using wordTrace_append hprefix tailTrace_982412
  have hstable : (prefixWord ++ tailWord_982412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982412).length < 2 ^ (prefixWord ++ tailWord_982412).sum := by decide
  have hdescent : baseEnd_982412 < baseStart_982412 := by decide
  rcases family_descends (prefixWord ++ tailWord_982412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982429 : List Nat := [1, 4, 2, 1, 3, 2, 1, 3, 4]
def baseStart_982429 : Nat := 118140960795 + 982429 * 2 ^ 59
def prefixEnd_982429 : Nat := 4983230072969 + 3 ^ 40 * 982429 * 2
def baseEnd_982429 : Nat := 224203682629351989208621

theorem tailTrace_982429 : CollatzResearch.WordTrace tailWord_982429 prefixEnd_982429 224203682629351989208621 := by
  unfold tailWord_982429
  simp only [CollatzResearch.WordTrace]
  refine ⟨35832129357834993360222341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23888086238556662240148227 35832129357834993360222341)
  ·
    refine ⟨6718524254594061255041689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35832129357834993360222341 6718524254594061255041689)
    ·
      refine ⟨5038893190945545941281267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6718524254594061255041689 5038893190945545941281267)
      ·
        refine ⟨7558339786418318911921901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5038893190945545941281267 7558339786418318911921901)
        ·
          refine ⟨2834377419906869591970713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7558339786418318911921901 2834377419906869591970713)
          ·
            refine ⟨2125783064930152193978035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2834377419906869591970713 2125783064930152193978035)
            ·
              refine ⟨3188674597395228290967053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2125783064930152193978035 3188674597395228290967053)
              ·
                refine ⟨1195752974023210609112645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3188674597395228290967053 1195752974023210609112645)
                ·
                  refine ⟨224203682629351989208621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1195752974023210609112645 224203682629351989208621)
                  ·
                    rfl

theorem cell21_982429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_982429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_982429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_982429 prefixEnd_982429 := by exact prefixLift 982429
  have htrace : WordTrace (prefixWord ++ tailWord_982429) baseStart_982429 baseEnd_982429 := by
    simpa [prefixWord, tailWord_982429, baseEnd_982429] using wordTrace_append hprefix tailTrace_982429
  have hstable : (prefixWord ++ tailWord_982429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982429).length < 2 ^ (prefixWord ++ tailWord_982429).sum := by decide
  have hdescent : baseEnd_982429 < baseStart_982429 := by decide
  rcases family_descends (prefixWord ++ tailWord_982429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982488 : List Nat := [2, 1, 2, 2, 2, 1, 4, 3, 4]
def baseStart_982488 : Nat := 118140960795 + 982488 * 2 ^ 59
def prefixEnd_982488 : Nat := 4983230072969 + 3 ^ 40 * 982488 * 2
def baseEnd_982488 : Nat := 224217147233180997725167

theorem tailTrace_982488 : CollatzResearch.WordTrace tailWord_982488 prefixEnd_982488 224217147233180997725167 := by
  unfold tailWord_982488
  simp only [CollatzResearch.WordTrace]
  refine ⟨17917140632310623218310059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23889520843080830957746745 17917140632310623218310059)
  ·
    refine ⟨26875710948465934827465089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17917140632310623218310059 26875710948465934827465089)
    ·
      refine ⟨20156783211349451120598817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26875710948465934827465089 20156783211349451120598817)
      ·
        refine ⟨15117587408512088340449113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20156783211349451120598817 15117587408512088340449113)
        ·
          refine ⟨11338190556384066255336835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15117587408512088340449113 11338190556384066255336835)
          ·
            refine ⟨17007285834576099383005253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11338190556384066255336835 17007285834576099383005253)
            ·
              refine ⟨3188866093983018634313485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17007285834576099383005253 3188866093983018634313485)
              ·
                refine ⟨1195824785243631987867557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3188866093983018634313485 1195824785243631987867557)
                ·
                  refine ⟨224217147233180997725167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1195824785243631987867557 224217147233180997725167)
                  ·
                    rfl

theorem cell21_982488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3, 4].length) (baseStart_982488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_982488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_982488 prefixEnd_982488 := by exact prefixLift 982488
  have htrace : WordTrace (prefixWord ++ tailWord_982488) baseStart_982488 baseEnd_982488 := by
    simpa [prefixWord, tailWord_982488, baseEnd_982488] using wordTrace_append hprefix tailTrace_982488
  have hstable : (prefixWord ++ tailWord_982488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982488).length < 2 ^ (prefixWord ++ tailWord_982488).sum := by decide
  have hdescent : baseEnd_982488 < baseStart_982488 := by decide
  rcases family_descends (prefixWord ++ tailWord_982488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982640 : List Nat := [2, 1, 1, 1, 6, 1, 1, 4, 4]
def baseStart_982640 : Nat := 118140960795 + 982640 * 2 ^ 59
def prefixEnd_982640 : Nat := 4983230072969 + 3 ^ 40 * 982640 * 2
def baseEnd_982640 : Nat := 224251835704062511191523

theorem tailTrace_982640 : CollatzResearch.WordTrace tailWord_982640 prefixEnd_982640 224251835704062511191523 := by
  unfold tailWord_982640
  simp only [CollatzResearch.WordTrace]
  refine ⟨17919912580035288198076687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23893216773380384264102249 17919912580035288198076687)
  ·
    refine ⟨26879868870052932297115031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17919912580035288198076687 26879868870052932297115031)
    ·
      refine ⟨40319803305079398445672547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26879868870052932297115031 40319803305079398445672547)
      ·
        refine ⟨60479704957619097668508821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40319803305079398445672547 60479704957619097668508821)
        ·
          refine ⟨2834986169888395203211351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 60479704957619097668508821 2834986169888395203211351)
          ·
            refine ⟨4252479254832592804817027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2834986169888395203211351 4252479254832592804817027)
            ·
              refine ⟨6378718882248889207225541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4252479254832592804817027 6378718882248889207225541)
              ·
                refine ⟨1196009790421666726354789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6378718882248889207225541 1196009790421666726354789)
                ·
                  refine ⟨224251835704062511191523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1196009790421666726354789 224251835704062511191523)
                  ·
                    rfl

theorem cell21_982640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4, 4].length) (baseStart_982640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_982640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_982640 prefixEnd_982640 := by exact prefixLift 982640
  have htrace : WordTrace (prefixWord ++ tailWord_982640) baseStart_982640 baseEnd_982640 := by
    simpa [prefixWord, tailWord_982640, baseEnd_982640] using wordTrace_append hprefix tailTrace_982640
  have hstable : (prefixWord ++ tailWord_982640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982640).length < 2 ^ (prefixWord ++ tailWord_982640).sum := by decide
  have hdescent : baseEnd_982640 < baseStart_982640 := by decide
  rcases family_descends (prefixWord ++ tailWord_982640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982733 : List Nat := [1, 6, 2, 1, 1, 1, 1, 2, 6]
def baseStart_982733 : Nat := 118140960795 + 982733 * 2 ^ 59
def prefixEnd_982733 : Nat := 4983230072969 + 3 ^ 40 * 982733 * 2
def baseEnd_982733 : Nat := 224273059571115016141333

theorem tailTrace_982733 : CollatzResearch.WordTrace tailWord_982733 prefixEnd_982733 224273059571115016141333 := by
  unfold tailWord_982733
  simp only [CollatzResearch.WordTrace]
  refine ⟨35843217148733653279288853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23895478099155768852859235 35843217148733653279288853)
  ·
    refine ⟨1680150803846889997466665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35843217148733653279288853 1680150803846889997466665)
    ·
      refine ⟨1260113102885167498099999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1680150803846889997466665 1260113102885167498099999)
      ·
        refine ⟨1890169654327751247149999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1260113102885167498099999 1890169654327751247149999)
        ·
          refine ⟨2835254481491626870724999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1890169654327751247149999 2835254481491626870724999)
          ·
            refine ⟨4252881722237440306087499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2835254481491626870724999 4252881722237440306087499)
            ·
              refine ⟨6379322583356160459131249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4252881722237440306087499 6379322583356160459131249)
              ·
                refine ⟨4784491937517120344348437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6379322583356160459131249 4784491937517120344348437)
                ·
                  refine ⟨224273059571115016141333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4784491937517120344348437 224273059571115016141333)
                  ·
                    rfl

theorem cell21_982733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_982733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_982733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_982733 prefixEnd_982733 := by exact prefixLift 982733
  have htrace : WordTrace (prefixWord ++ tailWord_982733) baseStart_982733 baseEnd_982733 := by
    simpa [prefixWord, tailWord_982733, baseEnd_982733] using wordTrace_append hprefix tailTrace_982733
  have hstable : (prefixWord ++ tailWord_982733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982733).length < 2 ^ (prefixWord ++ tailWord_982733).sum := by decide
  have hdescent : baseEnd_982733 < baseStart_982733 := by decide
  rcases family_descends (prefixWord ++ tailWord_982733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982868 : List Nat := [2, 4, 1, 1, 3, 2, 1, 1, 6]
def baseStart_982868 : Nat := 118140960795 + 982868 * 2 ^ 59
def prefixEnd_982868 : Nat := 4983230072969 + 3 ^ 40 * 982868 * 2
def baseEnd_982868 : Nat := 224303868410384781391057

theorem tailTrace_982868 : CollatzResearch.WordTrace tailWord_982868 prefixEnd_982868 224303868410384781391057 := by
  unfold tailWord_982868
  simp only [CollatzResearch.WordTrace]
  refine ⟨17924070501622285667726629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23898760668829714223635505 17924070501622285667726629)
  ·
    refine ⟨3360763219054178562698743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17924070501622285667726629 3360763219054178562698743)
    ·
      refine ⟨5041144828581267844048115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3360763219054178562698743 5041144828581267844048115)
      ·
        refine ⟨7561717242871901766072173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5041144828581267844048115 7561717242871901766072173)
        ·
          refine ⟨2835643966076963162277065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7561717242871901766072173 2835643966076963162277065)
          ·
            refine ⟨2126732974557722371707799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2835643966076963162277065 2126732974557722371707799)
            ·
              refine ⟨3190099461836583557561699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2126732974557722371707799 3190099461836583557561699)
              ·
                refine ⟨4785149192754875336342549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3190099461836583557561699 4785149192754875336342549)
                ·
                  refine ⟨224303868410384781391057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4785149192754875336342549 224303868410384781391057)
                  ·
                    rfl

theorem cell21_982868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_982868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_982868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_982868 prefixEnd_982868 := by exact prefixLift 982868
  have htrace : WordTrace (prefixWord ++ tailWord_982868) baseStart_982868 baseEnd_982868 := by
    simpa [prefixWord, tailWord_982868, baseEnd_982868] using wordTrace_append hprefix tailTrace_982868
  have hstable : (prefixWord ++ tailWord_982868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982868).length < 2 ^ (prefixWord ++ tailWord_982868).sum := by decide
  have hdescent : baseEnd_982868 < baseStart_982868 := by decide
  rcases family_descends (prefixWord ++ tailWord_982868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982930 : List Nat := [3, 2, 3, 2, 1, 1, 3, 1, 5]
def baseStart_982930 : Nat := 118140960795 + 982930 * 2 ^ 59
def prefixEnd_982930 : Nat := 4983230072969 + 3 ^ 40 * 982930 * 2
def baseEnd_982930 : Nat := 224318017655086451357597

theorem tailTrace_982930 : CollatzResearch.WordTrace tailWord_982930 prefixEnd_982930 224318017655086451357597 := by
  unfold tailWord_982930
  simp only [CollatzResearch.WordTrace]
  refine ⟨8962600582254988981052561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23900268219346637282806829 8962600582254988981052561)
  ·
    refine ⟨6721950436691241735789421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8962600582254988981052561 6721950436691241735789421)
    ·
      refine ⟨2520731413759215650921033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6721950436691241735789421 2520731413759215650921033)
      ·
        refine ⟨1890548560319411738190775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2520731413759215650921033 1890548560319411738190775)
        ·
          refine ⟨2835822840479117607286163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1890548560319411738190775 2835822840479117607286163)
          ·
            refine ⟨4253734260718676410929245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2835822840479117607286163 4253734260718676410929245)
            ·
              refine ⟨1595150347769503654098467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4253734260718676410929245 1595150347769503654098467)
              ·
                refine ⟨2392725521654255481147701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1595150347769503654098467 2392725521654255481147701)
                ·
                  refine ⟨224318017655086451357597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2392725521654255481147701 224318017655086451357597)
                  ·
                    rfl

theorem cell21_982930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_982930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_982930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_982930 prefixEnd_982930 := by exact prefixLift 982930
  have htrace : WordTrace (prefixWord ++ tailWord_982930) baseStart_982930 baseEnd_982930 := by
    simpa [prefixWord, tailWord_982930, baseEnd_982930] using wordTrace_append hprefix tailTrace_982930
  have hstable : (prefixWord ++ tailWord_982930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982930).length < 2 ^ (prefixWord ++ tailWord_982930).sum := by decide
  have hdescent : baseEnd_982930 < baseStart_982930 := by decide
  rcases family_descends (prefixWord ++ tailWord_982930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
