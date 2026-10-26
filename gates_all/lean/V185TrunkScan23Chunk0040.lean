import V185TrunkScan23Chunk0039

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_237364 : List Nat := [2, 5, 1, 1, 2, 1, 1, 2, 3, 2, 3]
def baseStart_237364 : Nat := 118140960795 + 237364 * 2 ^ 59
def prefixEnd_237364 : Nat := 4983230072969 + 3 ^ 40 * 237364 * 2
def baseEnd_237364 : Nat := 121881822073914545958389

theorem tailTrace_237364 : CollatzResearch.WordTrace tailWord_237364 prefixEnd_237364 121881822073914545958389 := by
  unfold tailWord_237364
  simp only [CollatzResearch.WordTrace]
  refine ⟨4328688156039120694435573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5771584208052160925914097 4328688156039120694435573)
  ·
    refine ⟨405814514628667565103335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4328688156039120694435573 405814514628667565103335)
    ·
      refine ⟨608721771943001347655003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405814514628667565103335 608721771943001347655003)
      ·
        refine ⟨913082657914502021482505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 608721771943001347655003 913082657914502021482505)
        ·
          refine ⟨684811993435876516111879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 913082657914502021482505 684811993435876516111879)
          ·
            refine ⟨1027217990153814774167819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 684811993435876516111879 1027217990153814774167819)
            ·
              refine ⟨1540826985230722161251729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1027217990153814774167819 1540826985230722161251729)
              ·
                refine ⟨1155620238923041620938797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1540826985230722161251729 1155620238923041620938797)
                ·
                  refine ⟨433357589596140607852049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1155620238923041620938797 433357589596140607852049)
                  ·
                    refine ⟨325018192197105455889037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 433357589596140607852049 325018192197105455889037)
                    ·
                      refine ⟨121881822073914545958389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 325018192197105455889037 121881822073914545958389)
                      ·
                        rfl

theorem cell23_237364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_237364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_237364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_237364 prefixEnd_237364 := by exact prefixLift 237364
  have htrace : WordTrace (prefixWord ++ tailWord_237364) baseStart_237364 baseEnd_237364 := by
    simpa [prefixWord, tailWord_237364, baseEnd_237364] using wordTrace_append hprefix tailTrace_237364
  have hstable : (prefixWord ++ tailWord_237364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237364).length < 2 ^ (prefixWord ++ tailWord_237364).sum := by decide
  have hdescent : baseEnd_237364 < baseStart_237364 := by decide
  rcases family_descends (prefixWord ++ tailWord_237364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237374 : List Nat := [4, 2, 1, 2, 2, 2, 2, 1, 1, 2, 4]
def baseStart_237374 : Nat := 118140960795 + 237374 * 2 ^ 59
def prefixEnd_237374 : Nat := 4983230072969 + 3 ^ 40 * 237374 * 2
def baseEnd_237374 : Nat := 121886956880459506833343

theorem tailTrace_237374 : CollatzResearch.WordTrace tailWord_237374 prefixEnd_237374 121886956880459506833343 := by
  unfold tailWord_237374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1082217630255251637091897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5771827361361342064490117 1082217630255251637091897)
  ·
    refine ⟨811663222691438727818923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1082217630255251637091897 811663222691438727818923)
    ·
      refine ⟨1217494834037158091728385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 811663222691438727818923 1217494834037158091728385)
      ·
        refine ⟨913121125527868568796289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1217494834037158091728385 913121125527868568796289)
        ·
          refine ⟨684840844145901426597217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 913121125527868568796289 684840844145901426597217)
          ·
            refine ⟨513630633109426069947913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 684840844145901426597217 513630633109426069947913)
            ·
              refine ⟨385222974832069552460935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 513630633109426069947913 385222974832069552460935)
              ·
                refine ⟨577834462248104328691403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385222974832069552460935 577834462248104328691403)
                ·
                  refine ⟨866751693372156493037105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 577834462248104328691403 866751693372156493037105)
                  ·
                    refine ⟨650063770029117369777829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 866751693372156493037105 650063770029117369777829)
                    ·
                      refine ⟨121886956880459506833343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 650063770029117369777829 121886956880459506833343)
                      ·
                        rfl

theorem cell23_237374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_237374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_237374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_237374 prefixEnd_237374 := by exact prefixLift 237374
  have htrace : WordTrace (prefixWord ++ tailWord_237374) baseStart_237374 baseEnd_237374 := by
    simpa [prefixWord, tailWord_237374, baseEnd_237374] using wordTrace_append hprefix tailTrace_237374
  have hstable : (prefixWord ++ tailWord_237374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237374).length < 2 ^ (prefixWord ++ tailWord_237374).sum := by decide
  have hdescent : baseEnd_237374 < baseStart_237374 := by decide
  rcases family_descends (prefixWord ++ tailWord_237374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237417 : List Nat := [1, 2, 1, 1, 1, 3, 1, 4, 3, 4, 2]
def baseStart_237417 : Nat := 118140960795 + 237417 * 2 ^ 59
def prefixEnd_237417 : Nat := 4983230072969 + 3 ^ 40 * 237417 * 2
def baseEnd_237417 : Nat := 121909036548602838595645

theorem tailTrace_237417 : CollatzResearch.WordTrace tailWord_237417 prefixEnd_237417 121909036548602838595645 := by
  unfold tailWord_237417
  simp only [CollatzResearch.WordTrace]
  refine ⟨8659309380886231440550505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5772872920590820960367003 8659309380886231440550505)
  ·
    refine ⟨6494482035664673580412879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8659309380886231440550505 6494482035664673580412879)
    ·
      refine ⟨9741723053497010370619319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6494482035664673580412879 9741723053497010370619319)
      ·
        refine ⟨14612584580245515555928979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9741723053497010370619319 14612584580245515555928979)
        ·
          refine ⟨21918876870368273333893469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14612584580245515555928979 21918876870368273333893469)
          ·
            refine ⟨8219578826388102500210051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21918876870368273333893469 8219578826388102500210051)
            ·
              refine ⟨12329368239582153750315077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8219578826388102500210051 12329368239582153750315077)
              ·
                refine ⟨2311756544921653828184077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12329368239582153750315077 2311756544921653828184077)
                ·
                  refine ⟨866908704345620185569029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2311756544921653828184077 866908704345620185569029)
                  ·
                    refine ⟨162545382064803784794193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 866908704345620185569029 162545382064803784794193)
                    ·
                      refine ⟨121909036548602838595645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 162545382064803784794193 121909036548602838595645)
                      ·
                        rfl

theorem cell23_237417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 4, 2].length) (baseStart_237417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_237417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_237417 prefixEnd_237417 := by exact prefixLift 237417
  have htrace : WordTrace (prefixWord ++ tailWord_237417) baseStart_237417 baseEnd_237417 := by
    simpa [prefixWord, tailWord_237417, baseEnd_237417] using wordTrace_append hprefix tailTrace_237417
  have hstable : (prefixWord ++ tailWord_237417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237417).length < 2 ^ (prefixWord ++ tailWord_237417).sum := by decide
  have hdescent : baseEnd_237417 < baseStart_237417 := by decide
  rcases family_descends (prefixWord ++ tailWord_237417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237434 : List Nat := [3, 1, 1, 1, 1, 1, 7, 1, 1, 4, 2]
def baseStart_237434 : Nat := 118140960795 + 237434 * 2 ^ 59
def prefixEnd_237434 : Nat := 4983230072969 + 3 ^ 40 * 237434 * 2
def baseEnd_237434 : Nat := 121917765719729272083067

theorem tailTrace_237434 : CollatzResearch.WordTrace tailWord_237434 prefixEnd_237434 121917765719729272083067 := by
  unfold tailWord_237434
  simp only [CollatzResearch.WordTrace]
  refine ⟨2164982355456160835979839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5773286281216428895946237 2164982355456160835979839)
  ·
    refine ⟨3247473533184241253969759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2164982355456160835979839 3247473533184241253969759)
    ·
      refine ⟨4871210299776361880954639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3247473533184241253969759 4871210299776361880954639)
      ·
        refine ⟨7306815449664542821431959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4871210299776361880954639 7306815449664542821431959)
        ·
          refine ⟨10960223174496814232147939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7306815449664542821431959 10960223174496814232147939)
          ·
            refine ⟨16440334761745221348221909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10960223174496814232147939 16440334761745221348221909)
            ·
              refine ⟨385320345978403625348951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 16440334761745221348221909 385320345978403625348951)
              ·
                refine ⟨577980518967605438023427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385320345978403625348951 577980518967605438023427)
                ·
                  refine ⟨866970778451408157035141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 577980518967605438023427 866970778451408157035141)
                  ·
                    refine ⟨162557020959639029444089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 866970778451408157035141 162557020959639029444089)
                    ·
                      refine ⟨121917765719729272083067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 162557020959639029444089 121917765719729272083067)
                      ·
                        rfl

theorem cell23_237434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 1, 4, 2].length) (baseStart_237434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_237434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_237434 prefixEnd_237434 := by exact prefixLift 237434
  have htrace : WordTrace (prefixWord ++ tailWord_237434) baseStart_237434 baseEnd_237434 := by
    simpa [prefixWord, tailWord_237434, baseEnd_237434] using wordTrace_append hprefix tailTrace_237434
  have hstable : (prefixWord ++ tailWord_237434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237434).length < 2 ^ (prefixWord ++ tailWord_237434).sum := by decide
  have hdescent : baseEnd_237434 < baseStart_237434 := by decide
  rcases family_descends (prefixWord ++ tailWord_237434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237438 : List Nat := [4, 2, 3, 1, 1, 1, 1, 4, 1, 3, 2]
def baseStart_237438 : Nat := 118140960795 + 237438 * 2 ^ 59
def prefixEnd_237438 : Nat := 4983230072969 + 3 ^ 40 * 237438 * 2
def baseEnd_237438 : Nat := 121919819642347256433049

theorem tailTrace_237438 : CollatzResearch.WordTrace tailWord_237438 prefixEnd_237438 121919819642347256433049 := by
  unfold tailWord_237438
  simp only [CollatzResearch.WordTrace]
  refine ⟨1082509414226269003383121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5773383542540101351376645 1082509414226269003383121)
  ·
    refine ⟨811882060669701752537341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1082509414226269003383121 811882060669701752537341)
    ·
      refine ⟨304455772751138157201503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 811882060669701752537341 304455772751138157201503)
      ·
        refine ⟨456683659126707235802255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304455772751138157201503 456683659126707235802255)
        ·
          refine ⟨685025488690060853703383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456683659126707235802255 685025488690060853703383)
          ·
            refine ⟨1027538233035091280555075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 685025488690060853703383 1027538233035091280555075)
            ·
              refine ⟨1541307349552636920832613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1027538233035091280555075 1541307349552636920832613)
              ·
                refine ⟨288995128041119422656115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1541307349552636920832613 288995128041119422656115)
                ·
                  refine ⟨433492692061679133984173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 288995128041119422656115 433492692061679133984173)
                  ·
                    refine ⟨162559759523129675244065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 433492692061679133984173 162559759523129675244065)
                    ·
                      refine ⟨121919819642347256433049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 162559759523129675244065 121919819642347256433049)
                      ·
                        rfl

theorem cell23_237438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_237438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_237438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_237438 prefixEnd_237438 := by exact prefixLift 237438
  have htrace : WordTrace (prefixWord ++ tailWord_237438) baseStart_237438 baseEnd_237438 := by
    simpa [prefixWord, tailWord_237438, baseEnd_237438] using wordTrace_append hprefix tailTrace_237438
  have hstable : (prefixWord ++ tailWord_237438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237438).length < 2 ^ (prefixWord ++ tailWord_237438).sum := by decide
  have hdescent : baseEnd_237438 < baseStart_237438 := by decide
  rcases family_descends (prefixWord ++ tailWord_237438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237440 : List Nat := [2, 1, 1, 2, 1, 2, 3, 4, 7]
def baseStart_237440 : Nat := 118140960795 + 237440 * 2 ^ 59
def prefixEnd_237440 : Nat := 4983230072969 + 3 ^ 40 * 237440 * 2
def baseEnd_237440 : Nat := 13546760733739583178671

theorem tailTrace_237440 : CollatzResearch.WordTrace tailWord_237440 prefixEnd_237440 13546760733739583178671 := by
  unfold tailWord_237440
  simp only [CollatzResearch.WordTrace]
  refine ⟨4330074129901453184318887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5773432173201937579091849 4330074129901453184318887)
  ·
    refine ⟨6495111194852179776478331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4330074129901453184318887 6495111194852179776478331)
    ·
      refine ⟨9742666792278269664717497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6495111194852179776478331 9742666792278269664717497)
      ·
        refine ⟨7307000094208702248538123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9742666792278269664717497 7307000094208702248538123)
        ·
          refine ⟨10960500141313053372807185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7307000094208702248538123 10960500141313053372807185)
          ·
            refine ⟨8220375105984790029605389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10960500141313053372807185 8220375105984790029605389)
            ·
              refine ⟨3082640664744296261102021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8220375105984790029605389 3082640664744296261102021)
              ·
                refine ⟨577995124639555548956629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3082640664744296261102021 577995124639555548956629)
                ·
                  refine ⟨13546760733739583178671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 577995124639555548956629 13546760733739583178671)
                  ·
                    rfl

theorem cell23_237440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 7].length) (baseStart_237440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_237440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_237440 prefixEnd_237440 := by exact prefixLift 237440
  have htrace : WordTrace (prefixWord ++ tailWord_237440) baseStart_237440 baseEnd_237440 := by
    simpa [prefixWord, tailWord_237440, baseEnd_237440] using wordTrace_append hprefix tailTrace_237440
  have hstable : (prefixWord ++ tailWord_237440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237440).length < 2 ^ (prefixWord ++ tailWord_237440).sum := by decide
  have hdescent : baseEnd_237440 < baseStart_237440 := by decide
  rcases family_descends (prefixWord ++ tailWord_237440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237524 : List Nat := [2, 4, 1, 2, 1, 1, 1, 4, 2, 1, 4]
def baseStart_237524 : Nat := 118140960795 + 237524 * 2 ^ 59
def prefixEnd_237524 : Nat := 4983230072969 + 3 ^ 40 * 237524 * 2
def baseEnd_237524 : Nat := 121963978978633919957653

theorem tailTrace_237524 : CollatzResearch.WordTrace tailWord_237524 prefixEnd_237524 121963978978633919957653 := by
  unfold tailWord_237524
  simp only [CollatzResearch.WordTrace]
  refine ⟨4331605995749294357347813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5775474660999059143130417 4331605995749294357347813)
  ·
    refine ⟨812176124202992692002715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4331605995749294357347813 812176124202992692002715)
    ·
      refine ⟨1218264186304489038004073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 812176124202992692002715 1218264186304489038004073)
      ·
        refine ⟨913698139728366778503055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1218264186304489038004073 913698139728366778503055)
        ·
          refine ⟨1370547209592550167754583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 913698139728366778503055 1370547209592550167754583)
          ·
            refine ⟨2055820814388825251631875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1370547209592550167754583 2055820814388825251631875)
            ·
              refine ⟨3083731221583237877447813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2055820814388825251631875 3083731221583237877447813)
              ·
                refine ⟨578199604046857102021465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3083731221583237877447813 578199604046857102021465)
                ·
                  refine ⟨433649703035142826516099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 578199604046857102021465 433649703035142826516099)
                  ·
                    refine ⟨650474554552714239774149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 433649703035142826516099 650474554552714239774149)
                    ·
                      refine ⟨121963978978633919957653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 650474554552714239774149 121963978978633919957653)
                      ·
                        rfl

theorem cell23_237524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_237524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_237524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_237524 prefixEnd_237524 := by exact prefixLift 237524
  have htrace : WordTrace (prefixWord ++ tailWord_237524) baseStart_237524 baseEnd_237524 := by
    simpa [prefixWord, tailWord_237524, baseEnd_237524] using wordTrace_append hprefix tailTrace_237524
  have hstable : (prefixWord ++ tailWord_237524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237524).length < 2 ^ (prefixWord ++ tailWord_237524).sum := by decide
  have hdescent : baseEnd_237524 < baseStart_237524 := by decide
  rcases family_descends (prefixWord ++ tailWord_237524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237558 : List Nat := [5, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4]
def baseStart_237558 : Nat := 118140960795 + 237558 * 2 ^ 59
def prefixEnd_237558 : Nat := 4983230072969 + 3 ^ 40 * 237558 * 2
def baseEnd_237558 : Nat := 121981437320886786932497

theorem tailTrace_237558 : CollatzResearch.WordTrace tailWord_237558 prefixEnd_237558 121981437320886786932497 := by
  unfold tailWord_237558
  simp only [CollatzResearch.WordTrace]
  refine ⟨541528254585963282589583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5776301382250275014288885 541528254585963282589583)
  ·
    refine ⟨812292381878944923884375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 541528254585963282589583 812292381878944923884375)
    ·
      refine ⟨1218438572818417385826563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 812292381878944923884375 1218438572818417385826563)
      ·
        refine ⟨1827657859227626078739845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1218438572818417385826563 1827657859227626078739845)
        ·
          refine ⟨342685848605179889763721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1827657859227626078739845 342685848605179889763721)
          ·
            refine ⟨257014386453884917322791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342685848605179889763721 257014386453884917322791)
            ·
              refine ⟨385521579680827375984187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257014386453884917322791 385521579680827375984187)
              ·
                refine ⟨578282369521241063976281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385521579680827375984187 578282369521241063976281)
                ·
                  refine ⟨433711777140930797982211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 578282369521241063976281 433711777140930797982211)
                  ·
                    refine ⟨650567665711396196973317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 433711777140930797982211 650567665711396196973317)
                    ·
                      refine ⟨121981437320886786932497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 650567665711396196973317 121981437320886786932497)
                      ·
                        rfl

theorem cell23_237558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_237558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_237558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_237558 prefixEnd_237558 := by exact prefixLift 237558
  have htrace : WordTrace (prefixWord ++ tailWord_237558) baseStart_237558 baseEnd_237558 := by
    simpa [prefixWord, tailWord_237558, baseEnd_237558] using wordTrace_append hprefix tailTrace_237558
  have hstable : (prefixWord ++ tailWord_237558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237558).length < 2 ^ (prefixWord ++ tailWord_237558).sum := by decide
  have hdescent : baseEnd_237558 < baseStart_237558 := by decide
  rcases family_descends (prefixWord ++ tailWord_237558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237561 : List Nat := [1, 2, 1, 3, 1, 6, 1, 1, 2, 2, 3]
def baseStart_237561 : Nat := 118140960795 + 237561 * 2 ^ 59
def prefixEnd_237561 : Nat := 4983230072969 + 3 ^ 40 * 237561 * 2
def baseEnd_237561 : Nat := 121982977762850275194983

theorem tailTrace_237561 : CollatzResearch.WordTrace tailWord_237561 prefixEnd_237561 121982977762850275194983 := by
  unfold tailWord_237561
  simp only [CollatzResearch.WordTrace]
  refine ⟨8664561492364544033792537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5776374328243029355861691 8664561492364544033792537)
  ·
    refine ⟨6498421119273408025344403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8664561492364544033792537 6498421119273408025344403)
    ·
      refine ⟨9747631678910112038016605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6498421119273408025344403 9747631678910112038016605)
      ·
        refine ⟨3655361879591292014256227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9747631678910112038016605 3655361879591292014256227)
        ·
          refine ⟨5483042819386938021384341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3655361879591292014256227 5483042819386938021384341)
          ·
            refine ⟨257017632158762719752391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5483042819386938021384341 257017632158762719752391)
            ·
              refine ⟨385526448238144079628587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257017632158762719752391 385526448238144079628587)
              ·
                refine ⟨578289672357216119442881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385526448238144079628587 578289672357216119442881)
                ·
                  refine ⟨433717254267912089582161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 578289672357216119442881 433717254267912089582161)
                  ·
                    refine ⟨325287940700934067186621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 433717254267912089582161 325287940700934067186621)
                    ·
                      refine ⟨121982977762850275194983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 325287940700934067186621 121982977762850275194983)
                      ·
                        rfl

theorem cell23_237561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 2, 2, 3].length) (baseStart_237561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_237561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_237561 prefixEnd_237561 := by exact prefixLift 237561
  have htrace : WordTrace (prefixWord ++ tailWord_237561) baseStart_237561 baseEnd_237561 := by
    simpa [prefixWord, tailWord_237561, baseEnd_237561] using wordTrace_append hprefix tailTrace_237561
  have hstable : (prefixWord ++ tailWord_237561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237561).length < 2 ^ (prefixWord ++ tailWord_237561).sum := by decide
  have hdescent : baseEnd_237561 < baseStart_237561 := by decide
  rcases family_descends (prefixWord ++ tailWord_237561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237631 : List Nat := [1, 1, 2, 2, 3, 1, 2, 2, 5, 2, 2]
def baseStart_237631 : Nat := 118140960795 + 237631 * 2 ^ 59
def prefixEnd_237631 : Nat := 4983230072969 + 3 ^ 40 * 237631 * 2
def baseEnd_237631 : Nat := 122018921408665001319661

theorem tailTrace_237631 : CollatzResearch.WordTrace tailWord_237631 prefixEnd_237631 122018921408665001319661 := by
  unfold tailWord_237631
  simp only [CollatzResearch.WordTrace]
  refine ⟨8667114602110945988840747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5778076401407297325893831 8667114602110945988840747)
  ·
    refine ⟨13000671903166418983261121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8667114602110945988840747 13000671903166418983261121)
    ·
      refine ⟨9750503927374814237445841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13000671903166418983261121 9750503927374814237445841)
      ·
        refine ⟨7312877945531110678084381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9750503927374814237445841 7312877945531110678084381)
        ·
          refine ⟨2742329229574166504281643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7312877945531110678084381 2742329229574166504281643)
          ·
            refine ⟨4113493844361249756422465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2742329229574166504281643 4113493844361249756422465)
            ·
              refine ⟨3085120383270937317316849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4113493844361249756422465 3085120383270937317316849)
              ·
                refine ⟨2313840287453202987987637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3085120383270937317316849 2313840287453202987987637)
                ·
                  refine ⟨216922526948737780123841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2313840287453202987987637 216922526948737780123841)
                  ·
                    refine ⟨162691895211553335092881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 216922526948737780123841 162691895211553335092881)
                    ·
                      refine ⟨122018921408665001319661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 162691895211553335092881 122018921408665001319661)
                      ·
                        rfl

theorem cell23_237631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 5, 2, 2].length) (baseStart_237631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_237631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_237631 prefixEnd_237631 := by exact prefixLift 237631
  have htrace : WordTrace (prefixWord ++ tailWord_237631) baseStart_237631 baseEnd_237631 := by
    simpa [prefixWord, tailWord_237631, baseEnd_237631] using wordTrace_append hprefix tailTrace_237631
  have hstable : (prefixWord ++ tailWord_237631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237631).length < 2 ^ (prefixWord ++ tailWord_237631).sum := by decide
  have hdescent : baseEnd_237631 < baseStart_237631 := by decide
  rcases family_descends (prefixWord ++ tailWord_237631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237657 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 2, 2, 6]
def baseStart_237657 : Nat := 118140960795 + 237657 * 2 ^ 59
def prefixEnd_237657 : Nat := 4983230072969 + 3 ^ 40 * 237657 * 2
def baseEnd_237657 : Nat := 122032271905681899594541

theorem tailTrace_237657 : CollatzResearch.WordTrace tailWord_237657 prefixEnd_237657 122032271905681899594541 := by
  unfold tailWord_237657
  simp only [CollatzResearch.WordTrace]
  refine ⟨8668062900016752429287225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5778708600011168286191483 8668062900016752429287225)
  ·
    refine ⟨6501047175012564321965419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8668062900016752429287225 6501047175012564321965419)
    ·
      refine ⟨9751570762518846482948129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6501047175012564321965419 9751570762518846482948129)
      ·
        refine ⟨7313678071889134862211097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9751570762518846482948129 7313678071889134862211097)
        ·
          refine ⟨5485258553916851146658323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7313678071889134862211097 5485258553916851146658323)
          ·
            refine ⟨8227887830875276719987485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5485258553916851146658323 8227887830875276719987485)
            ·
              refine ⟨3085457936578228769995307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8227887830875276719987485 3085457936578228769995307)
              ·
                refine ⟨4628186904867343154992961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3085457936578228769995307 4628186904867343154992961)
                ·
                  refine ⟨3471140178650507366244721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4628186904867343154992961 3471140178650507366244721)
                  ·
                    refine ⟨2603355133987880524683541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3471140178650507366244721 2603355133987880524683541)
                    ·
                      refine ⟨122032271905681899594541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2603355133987880524683541 122032271905681899594541)
                      ·
                        rfl

theorem cell23_237657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_237657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_237657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_237657 prefixEnd_237657 := by exact prefixLift 237657
  have htrace : WordTrace (prefixWord ++ tailWord_237657) baseStart_237657 baseEnd_237657 := by
    simpa [prefixWord, tailWord_237657, baseEnd_237657] using wordTrace_append hprefix tailTrace_237657
  have hstable : (prefixWord ++ tailWord_237657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237657).length < 2 ^ (prefixWord ++ tailWord_237657).sum := by decide
  have hdescent : baseEnd_237657 < baseStart_237657 := by decide
  rcases family_descends (prefixWord ++ tailWord_237657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237661 : List Nat := [1, 4, 4, 1, 1, 1, 2, 1, 1, 1, 6]
def baseStart_237661 : Nat := 118140960795 + 237661 * 2 ^ 59
def prefixEnd_237661 : Nat := 4983230072969 + 3 ^ 40 * 237661 * 2
def baseEnd_237661 : Nat := 122034325828299883944523

theorem tailTrace_237661 : CollatzResearch.WordTrace tailWord_237661 prefixEnd_237661 122034325828299883944523 := by
  unfold tailWord_237661
  simp only [CollatzResearch.WordTrace]
  refine ⟨8668208792002261112432837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5778805861334840741621891 8668208792002261112432837)
  ·
    refine ⟨1625289148500423958581157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8668208792002261112432837 1625289148500423958581157)
    ·
      refine ⟨304741715343829492233967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1625289148500423958581157 304741715343829492233967)
      ·
        refine ⟨457112573015744238350951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304741715343829492233967 457112573015744238350951)
        ·
          refine ⟨685668859523616357526427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457112573015744238350951 685668859523616357526427)
          ·
            refine ⟨1028503289285424536289641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 685668859523616357526427 1028503289285424536289641)
            ·
              refine ⟨771377466964068402217231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1028503289285424536289641 771377466964068402217231)
              ·
                refine ⟨1157066200446102603325847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 771377466964068402217231 1157066200446102603325847)
                ·
                  refine ⟨1735599300669153904988771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1157066200446102603325847 1735599300669153904988771)
                  ·
                    refine ⟨2603398951003730857483157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1735599300669153904988771 2603398951003730857483157)
                    ·
                      refine ⟨122034325828299883944523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2603398951003730857483157 122034325828299883944523)
                      ·
                        rfl

theorem cell23_237661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_237661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_237661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_237661 prefixEnd_237661 := by exact prefixLift 237661
  have htrace : WordTrace (prefixWord ++ tailWord_237661) baseStart_237661 baseEnd_237661 := by
    simpa [prefixWord, tailWord_237661, baseEnd_237661] using wordTrace_append hprefix tailTrace_237661
  have hstable : (prefixWord ++ tailWord_237661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237661).length < 2 ^ (prefixWord ++ tailWord_237661).sum := by decide
  have hdescent : baseEnd_237661 < baseStart_237661 := by decide
  rcases family_descends (prefixWord ++ tailWord_237661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237662 : List Nat := [4, 4, 1, 1, 2, 2, 1, 2, 1, 5]
def baseStart_237662 : Nat := 118140960795 + 237662 * 2 ^ 59
def prefixEnd_237662 : Nat := 4983230072969 + 3 ^ 40 * 237662 * 2
def baseEnd_237662 : Nat := 40678279769651460010673

theorem tailTrace_237662 : CollatzResearch.WordTrace tailWord_237662 prefixEnd_237662 40678279769651460010673 := by
  unfold tailWord_237662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1083530658124829785402405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5778830176665758855479493 1083530658124829785402405)
  ·
    refine ⟨203161998398405584762951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1083530658124829785402405 203161998398405584762951)
    ·
      refine ⟨304742997597608377144427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203161998398405584762951 304742997597608377144427)
      ·
        refine ⟨457114496396412565716641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304742997597608377144427 457114496396412565716641)
        ·
          refine ⟨342835872297309424287481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 457114496396412565716641 342835872297309424287481)
          ·
            refine ⟨257126904222982068215611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342835872297309424287481 257126904222982068215611)
            ·
              refine ⟨385690356334473102323417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257126904222982068215611 385690356334473102323417)
              ·
                refine ⟨289267767250854826742563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 385690356334473102323417 289267767250854826742563)
                ·
                  refine ⟨433901650876282240113845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 289267767250854826742563 433901650876282240113845)
                  ·
                    refine ⟨40678279769651460010673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 433901650876282240113845 40678279769651460010673)
                    ·
                      rfl

theorem cell23_237662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_237662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_237662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_237662 prefixEnd_237662 := by exact prefixLift 237662
  have htrace : WordTrace (prefixWord ++ tailWord_237662) baseStart_237662 baseEnd_237662 := by
    simpa [prefixWord, tailWord_237662, baseEnd_237662] using wordTrace_append hprefix tailTrace_237662
  have hstable : (prefixWord ++ tailWord_237662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237662).length < 2 ^ (prefixWord ++ tailWord_237662).sum := by decide
  have hdescent : baseEnd_237662 < baseStart_237662 := by decide
  rcases family_descends (prefixWord ++ tailWord_237662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237749 : List Nat := [1, 3, 3, 4, 2, 1, 1, 2, 2, 1, 3]
def baseStart_237749 : Nat := 118140960795 + 237749 * 2 ^ 59
def prefixEnd_237749 : Nat := 4983230072969 + 3 ^ 40 * 237749 * 2
def baseEnd_237749 : Nat := 122079512125895539644119

theorem tailTrace_237749 : CollatzResearch.WordTrace tailWord_237749 prefixEnd_237749 122079512125895539644119 := by
  unfold tailWord_237749
  simp only [CollatzResearch.WordTrace]
  refine ⟨8671418415683452141636301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5780945610455634761090867 8671418415683452141636301)
  ·
    refine ⟨3251781905881294553113613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8671418415683452141636301 3251781905881294553113613)
    ·
      refine ⟨1219418214705485457417605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3251781905881294553113613 1219418214705485457417605)
      ·
        refine ⟨228640915257278523265801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1219418214705485457417605 228640915257278523265801)
        ·
          refine ⟨171480686442958892449351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228640915257278523265801 171480686442958892449351)
          ·
            refine ⟨257221029664438338674027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171480686442958892449351 257221029664438338674027)
            ·
              refine ⟨385831544496657508011041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257221029664438338674027 385831544496657508011041)
              ·
                refine ⟨289373658372493131008281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 385831544496657508011041 289373658372493131008281)
                ·
                  refine ⟨217030243779369848256211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 289373658372493131008281 217030243779369848256211)
                  ·
                    refine ⟨325545365669054772384317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 217030243779369848256211 325545365669054772384317)
                    ·
                      refine ⟨122079512125895539644119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 325545365669054772384317 122079512125895539644119)
                      ·
                        rfl

theorem cell23_237749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_237749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_237749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_237749 prefixEnd_237749 := by exact prefixLift 237749
  have htrace : WordTrace (prefixWord ++ tailWord_237749) baseStart_237749 baseEnd_237749 := by
    simpa [prefixWord, tailWord_237749, baseEnd_237749] using wordTrace_append hprefix tailTrace_237749
  have hstable : (prefixWord ++ tailWord_237749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237749).length < 2 ^ (prefixWord ++ tailWord_237749).sum := by decide
  have hdescent : baseEnd_237749 < baseStart_237749 := by decide
  rcases family_descends (prefixWord ++ tailWord_237749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237772 : List Nat := [2, 2, 1, 6, 1, 2, 1, 1, 1, 4, 2]
def baseStart_237772 : Nat := 118140960795 + 237772 * 2 ^ 59
def prefixEnd_237772 : Nat := 4983230072969 + 3 ^ 40 * 237772 * 2
def baseEnd_237772 : Nat := 122091322180948949656513

theorem tailTrace_237772 : CollatzResearch.WordTrace tailWord_237772 prefixEnd_237772 122091322180948949656513 := by
  unfold tailWord_237772
  simp only [CollatzResearch.WordTrace]
  refine ⟨4336128647300063534861785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5781504863066751379815713 4336128647300063534861785)
  ·
    refine ⟨3252096485475047651146339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4336128647300063534861785 3252096485475047651146339)
    ·
      refine ⟨4878144728212571476719509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3252096485475047651146339 4878144728212571476719509)
      ·
        refine ⟨228663034134964287971227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4878144728212571476719509 228663034134964287971227)
        ·
          refine ⟨342994551202446431956841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228663034134964287971227 342994551202446431956841)
          ·
            refine ⟨257245913401834823967631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342994551202446431956841 257245913401834823967631)
            ·
              refine ⟨385868870102752235951447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257245913401834823967631 385868870102752235951447)
              ·
                refine ⟨578803305154128353927171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385868870102752235951447 578803305154128353927171)
                ·
                  refine ⟨868204957731192530890757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 578803305154128353927171 868204957731192530890757)
                  ·
                    refine ⟨162788429574598599542017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 868204957731192530890757 162788429574598599542017)
                    ·
                      refine ⟨122091322180948949656513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 162788429574598599542017 122091322180948949656513)
                      ·
                        rfl

theorem cell23_237772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_237772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_237772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_237772 prefixEnd_237772 := by exact prefixLift 237772
  have htrace : WordTrace (prefixWord ++ tailWord_237772) baseStart_237772 baseEnd_237772 := by
    simpa [prefixWord, tailWord_237772, baseEnd_237772] using wordTrace_append hprefix tailTrace_237772
  have hstable : (prefixWord ++ tailWord_237772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237772).length < 2 ^ (prefixWord ++ tailWord_237772).sum := by decide
  have hdescent : baseEnd_237772 < baseStart_237772 := by decide
  rcases family_descends (prefixWord ++ tailWord_237772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237811 : List Nat := [1, 1, 1, 2, 2, 4, 3, 2, 2, 1, 4]
def baseStart_237811 : Nat := 118140960795 + 237811 * 2 ^ 59
def prefixEnd_237811 : Nat := 4983230072969 + 3 ^ 40 * 237811 * 2
def baseEnd_237811 : Nat := 122111347926474297068833

theorem tailTrace_237811 : CollatzResearch.WordTrace tailWord_237811 prefixEnd_237811 122111347926474297068833 := by
  unfold tailWord_237811
  simp only [CollatzResearch.WordTrace]
  refine ⟨8673679741458836730393287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5782453160972557820262191 8673679741458836730393287)
  ·
    refine ⟨13010519612188255095589931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8673679741458836730393287 13010519612188255095589931)
    ·
      refine ⟨19515779418282382643384897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13010519612188255095589931 19515779418282382643384897)
      ·
        refine ⟨14636834563711786982538673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19515779418282382643384897 14636834563711786982538673)
        ·
          refine ⟨10977625922783840236904005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14636834563711786982538673 10977625922783840236904005)
          ·
            refine ⟨2058304860521970044419501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10977625922783840236904005 2058304860521970044419501)
            ·
              refine ⟨771864322695738766657313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2058304860521970044419501 771864322695738766657313)
              ·
                refine ⟨578898242021804074992985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 771864322695738766657313 578898242021804074992985)
                ·
                  refine ⟨434173681516353056244739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 578898242021804074992985 434173681516353056244739)
                  ·
                    refine ⟨651260522274529584367109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 434173681516353056244739 651260522274529584367109)
                    ·
                      refine ⟨122111347926474297068833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 651260522274529584367109 122111347926474297068833)
                      ·
                        rfl

theorem cell23_237811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2, 1, 4].length) (baseStart_237811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_237811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_237811 prefixEnd_237811 := by exact prefixLift 237811
  have htrace : WordTrace (prefixWord ++ tailWord_237811) baseStart_237811 baseEnd_237811 := by
    simpa [prefixWord, tailWord_237811, baseEnd_237811] using wordTrace_append hprefix tailTrace_237811
  have hstable : (prefixWord ++ tailWord_237811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237811).length < 2 ^ (prefixWord ++ tailWord_237811).sum := by decide
  have hdescent : baseEnd_237811 < baseStart_237811 := by decide
  rcases family_descends (prefixWord ++ tailWord_237811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237824 : List Nat := [2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 6]
def baseStart_237824 : Nat := 118140960795 + 237824 * 2 ^ 59
def prefixEnd_237824 : Nat := 4983230072969 + 3 ^ 40 * 237824 * 2
def baseEnd_237824 : Nat := 122118023174982746206273

theorem tailTrace_237824 : CollatzResearch.WordTrace tailWord_237824 prefixEnd_237824 122118023174982746206273 := by
  unfold tailWord_237824
  simp only [CollatzResearch.WordTrace]
  refine ⟨4337076945205869975308263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5782769260274493300411017 4337076945205869975308263)
  ·
    refine ⟨6505615417808804962962395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4337076945205869975308263 6505615417808804962962395)
    ·
      refine ⟨9758423126713207444443593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6505615417808804962962395 9758423126713207444443593)
      ·
        refine ⟨7318817345034905583332695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9758423126713207444443593 7318817345034905583332695)
        ·
          refine ⟨10978226017552358374999043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7318817345034905583332695 10978226017552358374999043)
          ·
            refine ⟨16467339026328537562498565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10978226017552358374999043 16467339026328537562498565)
            ·
              refine ⟨3087626067436600792968481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16467339026328537562498565 3087626067436600792968481)
              ·
                refine ⟨2315719550577450594726361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3087626067436600792968481 2315719550577450594726361)
                ·
                  refine ⟨1736789662933087946044771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2315719550577450594726361 1736789662933087946044771)
                  ·
                    refine ⟨2605184494399631919067157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1736789662933087946044771 2605184494399631919067157)
                    ·
                      refine ⟨122118023174982746206273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2605184494399631919067157 122118023174982746206273)
                      ·
                        rfl

theorem cell23_237824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_237824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_237824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_237824 prefixEnd_237824 := by exact prefixLift 237824
  have htrace : WordTrace (prefixWord ++ tailWord_237824) baseStart_237824 baseEnd_237824 := by
    simpa [prefixWord, tailWord_237824, baseEnd_237824] using wordTrace_append hprefix tailTrace_237824
  have hstable : (prefixWord ++ tailWord_237824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237824).length < 2 ^ (prefixWord ++ tailWord_237824).sum := by decide
  have hdescent : baseEnd_237824 < baseStart_237824 := by decide
  rcases family_descends (prefixWord ++ tailWord_237824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237848 : List Nat := [2, 1, 2, 3, 1, 2, 4, 1, 2, 2, 3]
def baseStart_237848 : Nat := 118140960795 + 237848 * 2 ^ 59
def prefixEnd_237848 : Nat := 4983230072969 + 3 ^ 40 * 237848 * 2
def baseEnd_237848 : Nat := 122130346710690652306163

theorem tailTrace_237848 : CollatzResearch.WordTrace tailWord_237848 prefixEnd_237848 122130346710690652306163 := by
  unfold tailWord_237848
  simp only [CollatzResearch.WordTrace]
  refine ⟨4337514621162396024745099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5783352828216528032993465 4337514621162396024745099)
  ·
    refine ⟨6506271931743594037117649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4337514621162396024745099 6506271931743594037117649)
    ·
      refine ⟨4879703948807695527838237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6506271931743594037117649 4879703948807695527838237)
      ·
        refine ⟨1829888980802885822939339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4879703948807695527838237 1829888980802885822939339)
        ·
          refine ⟨2744833471204328734409009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1829888980802885822939339 2744833471204328734409009)
          ·
            refine ⟨2058625103403246550806757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2744833471204328734409009 2058625103403246550806757)
            ·
              refine ⟨385992206888108728276267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2058625103403246550806757 385992206888108728276267)
              ·
                refine ⟨578988310332163092414401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385992206888108728276267 578988310332163092414401)
                ·
                  refine ⟨434241232749122319310801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 578988310332163092414401 434241232749122319310801)
                  ·
                    refine ⟨325680924561841739483101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 434241232749122319310801 325680924561841739483101)
                    ·
                      refine ⟨122130346710690652306163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 325680924561841739483101 122130346710690652306163)
                      ·
                        rfl

theorem cell23_237848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_237848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_237848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_237848 prefixEnd_237848 := by exact prefixLift 237848
  have htrace : WordTrace (prefixWord ++ tailWord_237848) baseStart_237848 baseEnd_237848 := by
    simpa [prefixWord, tailWord_237848, baseEnd_237848] using wordTrace_append hprefix tailTrace_237848
  have hstable : (prefixWord ++ tailWord_237848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237848).length < 2 ^ (prefixWord ++ tailWord_237848).sum := by decide
  have hdescent : baseEnd_237848 < baseStart_237848 := by decide
  rcases family_descends (prefixWord ++ tailWord_237848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237905 : List Nat := [1, 2, 2, 1, 4, 2, 3, 1, 2, 3, 2]
def baseStart_237905 : Nat := 118140960795 + 237905 * 2 ^ 59
def prefixEnd_237905 : Nat := 4983230072969 + 3 ^ 40 * 237905 * 2
def baseEnd_237905 : Nat := 122159615107996929293401

theorem tailTrace_237905 : CollatzResearch.WordTrace tailWord_237905 prefixEnd_237905 122159615107996929293401 := by
  unfold tailWord_237905
  simp only [CollatzResearch.WordTrace]
  refine ⟨8677108203118290784315169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5784738802078860522876779 8677108203118290784315169)
  ·
    refine ⟨6507831152338718088236377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8677108203118290784315169 6507831152338718088236377)
    ·
      refine ⟨4880873364254038566177283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6507831152338718088236377 4880873364254038566177283)
      ·
        refine ⟨7321310046381057849265925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4880873364254038566177283 7321310046381057849265925)
        ·
          refine ⟨1372745633696448346737361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7321310046381057849265925 1372745633696448346737361)
          ·
            refine ⟨1029559225272336260053021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1372745633696448346737361 1029559225272336260053021)
            ·
              refine ⟨386084709477126097519883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1029559225272336260053021 386084709477126097519883)
              ·
                refine ⟨579127064215689146279825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 386084709477126097519883 579127064215689146279825)
                ·
                  refine ⟨434345298161766859709869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 579127064215689146279825 434345298161766859709869)
                  ·
                    refine ⟨162879486810662572391201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 434345298161766859709869 162879486810662572391201)
                    ·
                      refine ⟨122159615107996929293401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 162879486810662572391201 122159615107996929293401)
                      ·
                        rfl

theorem cell23_237905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 2, 3, 2].length) (baseStart_237905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_237905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_237905 prefixEnd_237905 := by exact prefixLift 237905
  have htrace : WordTrace (prefixWord ++ tailWord_237905) baseStart_237905 baseEnd_237905 := by
    simpa [prefixWord, tailWord_237905, baseEnd_237905] using wordTrace_append hprefix tailTrace_237905
  have hstable : (prefixWord ++ tailWord_237905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237905).length < 2 ^ (prefixWord ++ tailWord_237905).sum := by decide
  have hdescent : baseEnd_237905 < baseStart_237905 := by decide
  rcases family_descends (prefixWord ++ tailWord_237905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237911 : List Nat := [1, 1, 3, 2, 3, 1, 1, 4, 1, 6]
def baseStart_237911 : Nat := 118140960795 + 237911 * 2 ^ 59
def prefixEnd_237911 : Nat := 4983230072969 + 3 ^ 40 * 237911 * 2
def baseEnd_237911 : Nat := 40720898663974635272791

theorem tailTrace_237911 : CollatzResearch.WordTrace tailWord_237911 prefixEnd_237911 40720898663974635272791 := by
  unfold tailWord_237911
  simp only [CollatzResearch.WordTrace]
  refine ⟨8677327041096553809033587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5784884694064369206022391 8677327041096553809033587)
  ·
    refine ⟨13015990561644830713550381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8677327041096553809033587 13015990561644830713550381)
    ·
      refine ⟨4880996460616811517581393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13015990561644830713550381 4880996460616811517581393)
      ·
        refine ⟨3660747345462608638186045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4880996460616811517581393 3660747345462608638186045)
        ·
          refine ⟨1372780254548478239319767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3660747345462608638186045 1372780254548478239319767)
          ·
            refine ⟨2059170381822717358979651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1372780254548478239319767 2059170381822717358979651)
            ·
              refine ⟨3088755572734076038469477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2059170381822717358979651 3088755572734076038469477)
              ·
                refine ⟨579141669887639257213027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3088755572734076038469477 579141669887639257213027)
                ·
                  refine ⟨868712504831458885819541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 579141669887639257213027 868712504831458885819541)
                  ·
                    refine ⟨40720898663974635272791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 868712504831458885819541 40720898663974635272791)
                    ·
                      rfl

theorem cell23_237911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 6].length) (baseStart_237911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_237911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_237911 prefixEnd_237911 := by exact prefixLift 237911
  have htrace : WordTrace (prefixWord ++ tailWord_237911) baseStart_237911 baseEnd_237911 := by
    simpa [prefixWord, tailWord_237911, baseEnd_237911] using wordTrace_append hprefix tailTrace_237911
  have hstable : (prefixWord ++ tailWord_237911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237911).length < 2 ^ (prefixWord ++ tailWord_237911).sum := by decide
  have hdescent : baseEnd_237911 < baseStart_237911 := by decide
  rcases family_descends (prefixWord ++ tailWord_237911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237938 : List Nat := [3, 2, 1, 2, 1, 4, 1, 2, 1, 1, 5]
def baseStart_237938 : Nat := 118140960795 + 237938 * 2 ^ 59
def prefixEnd_237938 : Nat := 4983230072969 + 3 ^ 40 * 237938 * 2
def baseEnd_237938 : Nat := 122176559969595300180749

theorem tailTrace_237938 : CollatzResearch.WordTrace tailWord_237938 prefixEnd_237938 122176559969595300180749 := by
  unfold tailWord_237938
  simp only [CollatzResearch.WordTrace]
  refine ⟨2169577952999684355066617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5785541207999158280177645 2169577952999684355066617)
  ·
    refine ⟨1627183464749763266299963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2169577952999684355066617 1627183464749763266299963)
    ·
      refine ⟨2440775197124644899449945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1627183464749763266299963 2440775197124644899449945)
      ·
        refine ⟨1830581397843483674587459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2440775197124644899449945 1830581397843483674587459)
        ·
          refine ⟨2745872096765225511881189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1830581397843483674587459 2745872096765225511881189)
          ·
            refine ⟨514851018143479783477723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2745872096765225511881189 514851018143479783477723)
            ·
              refine ⟨772276527215219675216585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 514851018143479783477723 772276527215219675216585)
              ·
                refine ⟨579207395411414756412439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 772276527215219675216585 579207395411414756412439)
                ·
                  refine ⟨868811093117122134618659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 579207395411414756412439 868811093117122134618659)
                  ·
                    refine ⟨1303216639675683201927989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 868811093117122134618659 1303216639675683201927989)
                    ·
                      refine ⟨122176559969595300180749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1303216639675683201927989 122176559969595300180749)
                      ·
                        rfl

theorem cell23_237938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_237938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_237938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_237938 prefixEnd_237938 := by exact prefixLift 237938
  have htrace : WordTrace (prefixWord ++ tailWord_237938) baseStart_237938 baseEnd_237938 := by
    simpa [prefixWord, tailWord_237938, baseEnd_237938] using wordTrace_append hprefix tailTrace_237938
  have hstable : (prefixWord ++ tailWord_237938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237938).length < 2 ^ (prefixWord ++ tailWord_237938).sum := by decide
  have hdescent : baseEnd_237938 < baseStart_237938 := by decide
  rcases family_descends (prefixWord ++ tailWord_237938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237986 : List Nat := [3, 3, 1, 2, 1, 1, 5, 2, 1, 2, 2]
def baseStart_237986 : Nat := 118140960795 + 237986 * 2 ^ 59
def prefixEnd_237986 : Nat := 4983230072969 + 3 ^ 40 * 237986 * 2
def baseEnd_237986 : Nat := 122201207041011112380529

theorem tailTrace_237986 : CollatzResearch.WordTrace tailWord_237986 prefixEnd_237986 122201207041011112380529 := by
  unfold tailWord_237986
  simp only [CollatzResearch.WordTrace]
  refine ⟨2170015628956210404503453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5786708343883227745342541 2170015628956210404503453)
  ·
    refine ⟨813755860858578901688795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2170015628956210404503453 813755860858578901688795)
    ·
      refine ⟨1220633791287868352533193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 813755860858578901688795 1220633791287868352533193)
      ·
        refine ⟨915475343465901264399895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1220633791287868352533193 915475343465901264399895)
        ·
          refine ⟨1373213015198851896599843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 915475343465901264399895 1373213015198851896599843)
          ·
            refine ⟨2059819522798277844899765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1373213015198851896599843 2059819522798277844899765)
            ·
              refine ⟨193108080262338547959353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2059819522798277844899765 193108080262338547959353)
              ·
                refine ⟨144831060196753910969515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193108080262338547959353 144831060196753910969515)
                ·
                  refine ⟨217246590295130866454273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144831060196753910969515 217246590295130866454273)
                  ·
                    refine ⟨162934942721348149840705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 217246590295130866454273 162934942721348149840705)
                    ·
                      refine ⟨122201207041011112380529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 162934942721348149840705 122201207041011112380529)
                      ·
                        rfl

theorem cell23_237986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_237986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_237986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_237986 prefixEnd_237986 := by exact prefixLift 237986
  have htrace : WordTrace (prefixWord ++ tailWord_237986) baseStart_237986 baseEnd_237986 := by
    simpa [prefixWord, tailWord_237986, baseEnd_237986] using wordTrace_append hprefix tailTrace_237986
  have hstable : (prefixWord ++ tailWord_237986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237986).length < 2 ^ (prefixWord ++ tailWord_237986).sum := by decide
  have hdescent : baseEnd_237986 < baseStart_237986 := by decide
  rcases family_descends (prefixWord ++ tailWord_237986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238012 : List Nat := [2, 2, 2, 4, 1, 2, 1, 1, 3, 3, 2]
def baseStart_238012 : Nat := 118140960795 + 238012 * 2 ^ 59
def prefixEnd_238012 : Nat := 4983230072969 + 3 ^ 40 * 238012 * 2
def baseEnd_238012 : Nat := 122214557538028010655409

theorem tailTrace_238012 : CollatzResearch.WordTrace tailWord_238012 prefixEnd_238012 122214557538028010655409 := by
  unfold tailWord_238012
  simp only [CollatzResearch.WordTrace]
  refine ⟨4340505406865324029230145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5787340542487098705640193 4340505406865324029230145)
  ·
    refine ⟨3255379055148993021922609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4340505406865324029230145 3255379055148993021922609)
    ·
      refine ⟨2441534291361744766441957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3255379055148993021922609 2441534291361744766441957)
      ·
        refine ⟨457787679630327143707867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2441534291361744766441957 457787679630327143707867)
        ·
          refine ⟨686681519445490715561801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457787679630327143707867 686681519445490715561801)
          ·
            refine ⟨515011139584118036671351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 686681519445490715561801 515011139584118036671351)
            ·
              refine ⟨772516709376177055007027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 515011139584118036671351 772516709376177055007027)
              ·
                refine ⟨1158775064064265582510541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 772516709376177055007027 1158775064064265582510541)
                ·
                  refine ⟨434540649024099593441453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1158775064064265582510541 434540649024099593441453)
                  ·
                    refine ⟨162952743384037347540545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 434540649024099593441453 162952743384037347540545)
                    ·
                      refine ⟨122214557538028010655409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 162952743384037347540545 122214557538028010655409)
                      ·
                        rfl

theorem cell23_238012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_238012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_238012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_238012 prefixEnd_238012 := by exact prefixLift 238012
  have htrace : WordTrace (prefixWord ++ tailWord_238012) baseStart_238012 baseEnd_238012 := by
    simpa [prefixWord, tailWord_238012, baseEnd_238012] using wordTrace_append hprefix tailTrace_238012
  have hstable : (prefixWord ++ tailWord_238012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238012).length < 2 ^ (prefixWord ++ tailWord_238012).sum := by decide
  have hdescent : baseEnd_238012 < baseStart_238012 := by decide
  rcases family_descends (prefixWord ++ tailWord_238012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238025 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 6, 2, 2]
def baseStart_238025 : Nat := 118140960795 + 238025 * 2 ^ 59
def prefixEnd_238025 : Nat := 4983230072969 + 3 ^ 40 * 238025 * 2
def baseEnd_238025 : Nat := 122221232786536459792849

theorem tailTrace_238025 : CollatzResearch.WordTrace tailWord_238025 prefixEnd_238025 122221232786536459792849 := by
  unfold tailWord_238025
  simp only [CollatzResearch.WordTrace]
  refine ⟨8681484962683551278683529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5787656641789034185789019 8681484962683551278683529)
  ·
    refine ⟨6511113722012663459012647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8681484962683551278683529 6511113722012663459012647)
    ·
      refine ⟨9766670583018995188518971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6511113722012663459012647 9766670583018995188518971)
      ·
        refine ⟨14650005874528492782778457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9766670583018995188518971 14650005874528492782778457)
        ·
          refine ⟨10987504405896369587083843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14650005874528492782778457 10987504405896369587083843)
          ·
            refine ⟨16481256608844554380625765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10987504405896369587083843 16481256608844554380625765)
            ·
              refine ⟨3090235614158353946367331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16481256608844554380625765 3090235614158353946367331)
              ·
                refine ⟨4635353421237530919550997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3090235614158353946367331 4635353421237530919550997)
                ·
                  refine ⟨217282191620509261853953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4635353421237530919550997 217282191620509261853953)
                  ·
                    refine ⟨162961643715381946390465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 217282191620509261853953 162961643715381946390465)
                    ·
                      refine ⟨122221232786536459792849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 162961643715381946390465 122221232786536459792849)
                      ·
                        rfl

theorem cell23_238025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 6, 2, 2].length) (baseStart_238025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_238025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_238025 prefixEnd_238025 := by exact prefixLift 238025
  have htrace : WordTrace (prefixWord ++ tailWord_238025) baseStart_238025 baseEnd_238025 := by
    simpa [prefixWord, tailWord_238025, baseEnd_238025] using wordTrace_append hprefix tailTrace_238025
  have hstable : (prefixWord ++ tailWord_238025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238025).length < 2 ^ (prefixWord ++ tailWord_238025).sum := by decide
  have hdescent : baseEnd_238025 < baseStart_238025 := by decide
  rcases family_descends (prefixWord ++ tailWord_238025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238093 : List Nat := [1, 7, 1, 1, 1, 1, 3, 2, 2, 2, 2]
def baseStart_238093 : Nat := 118140960795 + 238093 * 2 ^ 59
def prefixEnd_238093 : Nat := 4983230072969 + 3 ^ 40 * 238093 * 2
def baseEnd_238093 : Nat := 122256149471042193742537

theorem tailTrace_238093 : CollatzResearch.WordTrace tailWord_238093 prefixEnd_238093 122256149471042193742537 := by
  unfold tailWord_238093
  simp only [CollatzResearch.WordTrace]
  refine ⟨8683965126437198892158933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5789310084291465928105955 8683965126437198892158933)
  ·
    refine ⟨203530432650871849034975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 8683965126437198892158933 203530432650871849034975)
    ·
      refine ⟨305295648976307773552463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203530432650871849034975 305295648976307773552463)
      ·
        refine ⟨457943473464461660328695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305295648976307773552463 457943473464461660328695)
        ·
          refine ⟨686915210196692490493043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457943473464461660328695 686915210196692490493043)
          ·
            refine ⟨1030372815295038735739565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 686915210196692490493043 1030372815295038735739565)
            ·
              refine ⟨386389805735639525902337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1030372815295038735739565 386389805735639525902337)
              ·
                refine ⟨289792354301729644426753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 386389805735639525902337 289792354301729644426753)
                ·
                  refine ⟨217344265726297233320065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 289792354301729644426753 217344265726297233320065)
                  ·
                    refine ⟨163008199294722924990049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 217344265726297233320065 163008199294722924990049)
                    ·
                      refine ⟨122256149471042193742537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 163008199294722924990049 122256149471042193742537)
                      ·
                        rfl

theorem cell23_238093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_238093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_238093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_238093 prefixEnd_238093 := by exact prefixLift 238093
  have htrace : WordTrace (prefixWord ++ tailWord_238093) baseStart_238093 baseEnd_238093 := by
    simpa [prefixWord, tailWord_238093, baseEnd_238093] using wordTrace_append hprefix tailTrace_238093
  have hstable : (prefixWord ++ tailWord_238093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238093).length < 2 ^ (prefixWord ++ tailWord_238093).sum := by decide
  have hdescent : baseEnd_238093 < baseStart_238093 := by decide
  rcases family_descends (prefixWord ++ tailWord_238093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238135 : List Nat := [1, 1, 3, 1, 2, 3, 2, 3, 2, 2, 3]
def baseStart_238135 : Nat := 118140960795 + 238135 * 2 ^ 59
def prefixEnd_238135 : Nat := 4983230072969 + 3 ^ 40 * 238135 * 2
def baseEnd_238135 : Nat := 122277715658531029417343

theorem tailTrace_238135 : CollatzResearch.WordTrace tailWord_238135 prefixEnd_238135 122277715658531029417343 := by
  unfold tailWord_238135
  simp only [CollatzResearch.WordTrace]
  refine ⟨8685496992285040065187859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5790331328190026710125239 8685496992285040065187859)
  ·
    refine ⟨13028245488427560097781789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8685496992285040065187859 13028245488427560097781789)
    ·
      refine ⟨4885592058160335036668171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13028245488427560097781789 4885592058160335036668171)
      ·
        refine ⟨7328388087240502555002257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4885592058160335036668171 7328388087240502555002257)
        ·
          refine ⟨5496291065430376916251693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7328388087240502555002257 5496291065430376916251693)
          ·
            refine ⟨2061109149536391343594385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5496291065430376916251693 2061109149536391343594385)
            ·
              refine ⟨1545831862152293507695789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2061109149536391343594385 1545831862152293507695789)
              ·
                refine ⟨579686948307110065385921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1545831862152293507695789 579686948307110065385921)
                ·
                  refine ⟨434765211230332549039441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 579686948307110065385921 434765211230332549039441)
                  ·
                    refine ⟨326073908422749411779581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 434765211230332549039441 326073908422749411779581)
                    ·
                      refine ⟨122277715658531029417343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 326073908422749411779581 122277715658531029417343)
                      ·
                        rfl

theorem cell23_238135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2, 2, 3].length) (baseStart_238135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_238135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_238135 prefixEnd_238135 := by exact prefixLift 238135
  have htrace : WordTrace (prefixWord ++ tailWord_238135) baseStart_238135 baseEnd_238135 := by
    simpa [prefixWord, tailWord_238135, baseEnd_238135] using wordTrace_append hprefix tailTrace_238135
  have hstable : (prefixWord ++ tailWord_238135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238135).length < 2 ^ (prefixWord ++ tailWord_238135).sum := by decide
  have hdescent : baseEnd_238135 < baseStart_238135 := by decide
  rcases family_descends (prefixWord ++ tailWord_238135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238138 : List Nat := [3, 1, 1, 1, 3, 3, 1, 2, 8]
def baseStart_238138 : Nat := 118140960795 + 238138 * 2 ^ 59
def prefixEnd_238138 : Nat := 4983230072969 + 3 ^ 40 * 238138 * 2
def baseEnd_238138 : Nat := 13586584011166057519981

theorem tailTrace_238138 : CollatzResearch.WordTrace tailWord_238138 prefixEnd_238138 13586584011166057519981 := by
  unfold tailWord_238138
  simp only [CollatzResearch.WordTrace]
  refine ⟨2171401602818542894386767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5790404274182781051698045 2171401602818542894386767)
  ·
    refine ⟨3257102404227814341580151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2171401602818542894386767 3257102404227814341580151)
    ·
      refine ⟨4885653606341721512370227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3257102404227814341580151 4885653606341721512370227)
      ·
        refine ⟨7328480409512582268555341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4885653606341721512370227 7328480409512582268555341)
        ·
          refine ⟨2748180153567218350708253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7328480409512582268555341 2748180153567218350708253)
          ·
            refine ⟨1030567557587706881515595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2748180153567218350708253 1030567557587706881515595)
            ·
              refine ⟨1545851336381560322273393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1030567557587706881515595 1545851336381560322273393)
              ·
                refine ⟨1159388502286170241705045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1545851336381560322273393 1159388502286170241705045)
                ·
                  refine ⟨13586584011166057519981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1159388502286170241705045 13586584011166057519981)
                  ·
                    rfl

theorem cell23_238138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 8].length) (baseStart_238138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_238138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_238138 prefixEnd_238138 := by exact prefixLift 238138
  have htrace : WordTrace (prefixWord ++ tailWord_238138) baseStart_238138 baseEnd_238138 := by
    simpa [prefixWord, tailWord_238138, baseEnd_238138] using wordTrace_append hprefix tailTrace_238138
  have hstable : (prefixWord ++ tailWord_238138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238138).length < 2 ^ (prefixWord ++ tailWord_238138).sum := by decide
  have hdescent : baseEnd_238138 < baseStart_238138 := by decide
  rcases family_descends (prefixWord ++ tailWord_238138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238158 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8]
def baseStart_238158 : Nat := 118140960795 + 238158 * 2 ^ 59
def prefixEnd_238158 : Nat := 4983230072969 + 3 ^ 40 * 238158 * 2
def baseEnd_238158 : Nat := 122289525713584439429737

theorem tailTrace_238158 : CollatzResearch.WordTrace tailWord_238158 prefixEnd_238158 122289525713584439429737 := by
  unfold tailWord_238158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1085791983900214374159391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5790890580801143328850085 1085791983900214374159391)
  ·
    refine ⟨1628687975850321561239087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1085791983900214374159391 1628687975850321561239087)
    ·
      refine ⟨2443031963775482341858631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1628687975850321561239087 2443031963775482341858631)
      ·
        refine ⟨3664547945663223512787947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2443031963775482341858631 3664547945663223512787947)
        ·
          refine ⟨5496821918494835269181921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3664547945663223512787947 5496821918494835269181921)
          ·
            refine ⟨4122616438871126451886441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5496821918494835269181921 4122616438871126451886441)
            ·
              refine ⟨3091962329153344838914831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4122616438871126451886441 3091962329153344838914831)
              ·
                refine ⟨4637943493730017258372247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3091962329153344838914831 4637943493730017258372247)
                ·
                  refine ⟨6956915240595025887558371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4637943493730017258372247 6956915240595025887558371)
                  ·
                    refine ⟨10435372860892538831337557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6956915240595025887558371 10435372860892538831337557)
                    ·
                      refine ⟨122289525713584439429737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 10435372860892538831337557 122289525713584439429737)
                      ·
                        rfl

theorem cell23_238158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_238158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_238158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_238158 prefixEnd_238158 := by exact prefixLift 238158
  have htrace : WordTrace (prefixWord ++ tailWord_238158) baseStart_238158 baseEnd_238158 := by
    simpa [prefixWord, tailWord_238158, baseEnd_238158] using wordTrace_append hprefix tailTrace_238158
  have hstable : (prefixWord ++ tailWord_238158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238158).length < 2 ^ (prefixWord ++ tailWord_238158).sum := by decide
  have hdescent : baseEnd_238158 < baseStart_238158 := by decide
  rcases family_descends (prefixWord ++ tailWord_238158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238172 : List Nat := [2, 2, 4, 1, 3, 1, 1, 3, 6]
def baseStart_238172 : Nat := 118140960795 + 238172 * 2 ^ 59
def prefixEnd_238172 : Nat := 4983230072969 + 3 ^ 40 * 238172 * 2
def baseEnd_238172 : Nat := 13588523826971931628297

theorem tailTrace_238172 : CollatzResearch.WordTrace tailWord_238172 prefixEnd_238172 13588523826971931628297 := by
  unfold tailWord_238172
  simp only [CollatzResearch.WordTrace]
  refine ⟨4343423246575497692142385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5791230995433996922856513 4343423246575497692142385)
  ·
    refine ⟨3257567434931623269106789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4343423246575497692142385 3257567434931623269106789)
    ·
      refine ⟨610793894049679362957523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3257567434931623269106789 610793894049679362957523)
      ·
        refine ⟨916190841074519044436285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610793894049679362957523 916190841074519044436285)
        ·
          refine ⟨343571565402944641663607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 916190841074519044436285 343571565402944641663607)
          ·
            refine ⟨515357348104416962495411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343571565402944641663607 515357348104416962495411)
            ·
              refine ⟨773036022156625443743117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 515357348104416962495411 773036022156625443743117)
              ·
                refine ⟨289888508308734541403669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 773036022156625443743117 289888508308734541403669)
                ·
                  refine ⟨13588523826971931628297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 289888508308734541403669 13588523826971931628297)
                  ·
                    rfl

theorem cell23_238172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3, 6].length) (baseStart_238172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_238172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_238172 prefixEnd_238172 := by exact prefixLift 238172
  have htrace : WordTrace (prefixWord ++ tailWord_238172) baseStart_238172 baseEnd_238172 := by
    simpa [prefixWord, tailWord_238172, baseEnd_238172] using wordTrace_append hprefix tailTrace_238172
  have hstable : (prefixWord ++ tailWord_238172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238172).length < 2 ^ (prefixWord ++ tailWord_238172).sum := by decide
  have hdescent : baseEnd_238172 < baseStart_238172 := by decide
  rcases family_descends (prefixWord ++ tailWord_238172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238175 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 3, 5, 2]
def baseStart_238175 : Nat := 118140960795 + 238175 * 2 ^ 59
def prefixEnd_238175 : Nat := 4983230072969 + 3 ^ 40 * 238175 * 2
def baseEnd_238175 : Nat := 122298254884710872917159

theorem tailTrace_238175 : CollatzResearch.WordTrace tailWord_238175 prefixEnd_238175 122298254884710872917159 := by
  unfold tailWord_238175
  simp only [CollatzResearch.WordTrace]
  refine ⟨8686955912140126896643979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5791303941426751264429319 8686955912140126896643979)
  ·
    refine ⟨13030433868210190344965969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8686955912140126896643979 13030433868210190344965969)
    ·
      refine ⟨9772825401157642758724477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13030433868210190344965969 9772825401157642758724477)
      ·
        refine ⟨3664809525434116034521679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9772825401157642758724477 3664809525434116034521679)
        ·
          refine ⟨5497214288151174051782519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3664809525434116034521679 5497214288151174051782519)
          ·
            refine ⟨8245821432226761077673779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5497214288151174051782519 8245821432226761077673779)
            ·
              refine ⟨12368732148340141616510669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8245821432226761077673779 12368732148340141616510669)
              ·
                refine ⟨4638274555627553106191501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12368732148340141616510669 4638274555627553106191501)
                ·
                  refine ⟨1739352958360332414821813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4638274555627553106191501 1739352958360332414821813)
                  ·
                    refine ⟨163064339846281163889545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1739352958360332414821813 163064339846281163889545)
                    ·
                      refine ⟨122298254884710872917159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 163064339846281163889545 122298254884710872917159)
                      ·
                        rfl

theorem cell23_238175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 5, 2].length) (baseStart_238175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_238175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_238175 prefixEnd_238175 := by exact prefixLift 238175
  have htrace : WordTrace (prefixWord ++ tailWord_238175) baseStart_238175 baseEnd_238175 := by
    simpa [prefixWord, tailWord_238175, baseEnd_238175] using wordTrace_append hprefix tailTrace_238175
  have hstable : (prefixWord ++ tailWord_238175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238175).length < 2 ^ (prefixWord ++ tailWord_238175).sum := by decide
  have hdescent : baseEnd_238175 < baseStart_238175 := by decide
  rcases family_descends (prefixWord ++ tailWord_238175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238210 : List Nat := [3, 4, 3, 1, 1, 1, 1, 4, 1, 4]
def baseStart_238210 : Nat := 118140960795 + 238210 * 2 ^ 59
def prefixEnd_238210 : Nat := 4983230072969 + 3 ^ 40 * 238210 * 2
def baseEnd_238210 : Nat := 40772075569206078659833

theorem tailTrace_238210 : CollatzResearch.WordTrace tailWord_238210 prefixEnd_238210 40772075569206078659833 := by
  unfold tailWord_238210
  simp only [CollatzResearch.WordTrace]
  refine ⟨2172058116753331968542021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5792154978008885249445389 2172058116753331968542021)
  ·
    refine ⟨407260896891249744101629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2172058116753331968542021 407260896891249744101629)
    ·
      refine ⟨152722836334218654038111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 407260896891249744101629 152722836334218654038111)
      ·
        refine ⟨229084254501327981057167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152722836334218654038111 229084254501327981057167)
        ·
          refine ⟨343626381751991971585751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229084254501327981057167 343626381751991971585751)
          ·
            refine ⟨515439572627987957378627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343626381751991971585751 515439572627987957378627)
            ·
              refine ⟨773159358941981936067941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 515439572627987957378627 773159358941981936067941)
              ·
                refine ⟨144967379801621613012739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 773159358941981936067941 144967379801621613012739)
                ·
                  refine ⟨217451069702432419519109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144967379801621613012739 217451069702432419519109)
                  ·
                    refine ⟨40772075569206078659833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 217451069702432419519109 40772075569206078659833)
                    ·
                      rfl

theorem cell23_238210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_238210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_238210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_238210 prefixEnd_238210 := by exact prefixLift 238210
  have htrace : WordTrace (prefixWord ++ tailWord_238210) baseStart_238210 baseEnd_238210 := by
    simpa [prefixWord, tailWord_238210, baseEnd_238210] using wordTrace_append hprefix tailTrace_238210
  have hstable : (prefixWord ++ tailWord_238210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238210).length < 2 ^ (prefixWord ++ tailWord_238210).sum := by decide
  have hdescent : baseEnd_238210 < baseStart_238210 := by decide
  rcases family_descends (prefixWord ++ tailWord_238210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238232 : List Nat := [2, 1, 2, 4, 1, 1, 1, 5, 2, 4]
def baseStart_238232 : Nat := 118140960795 + 238232 * 2 ^ 59
def prefixEnd_238232 : Nat := 4983230072969 + 3 ^ 40 * 238232 * 2
def baseEnd_238232 : Nat := 40775841094005716634799

theorem tailTrace_238232 : CollatzResearch.WordTrace tailWord_238232 prefixEnd_238232 40775841094005716634799 := by
  unfold tailWord_238232
  simp only [CollatzResearch.WordTrace]
  refine ⟨4344517436466812815734475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5792689915289083754312633 4344517436466812815734475)
  ·
    refine ⟨6516776154700219223601713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4344517436466812815734475 6516776154700219223601713)
    ·
      refine ⟨4887582116025164417701285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6516776154700219223601713 4887582116025164417701285)
      ·
        refine ⟨916421646754718328318991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4887582116025164417701285 916421646754718328318991)
        ·
          refine ⟨1374632470132077492478487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 916421646754718328318991 1374632470132077492478487)
          ·
            refine ⟨2061948705198116238717731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1374632470132077492478487 2061948705198116238717731)
            ·
              refine ⟨3092923057797174358076597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2061948705198116238717731 3092923057797174358076597)
              ·
                refine ⟨289961536668485096069681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3092923057797174358076597 289961536668485096069681)
                ·
                  refine ⟨217471152501363822052261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 289961536668485096069681 217471152501363822052261)
                  ·
                    refine ⟨40775841094005716634799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 217471152501363822052261 40775841094005716634799)
                    ·
                      rfl

theorem cell23_238232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5, 2, 4].length) (baseStart_238232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_238232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_238232 prefixEnd_238232 := by exact prefixLift 238232
  have htrace : WordTrace (prefixWord ++ tailWord_238232) baseStart_238232 baseEnd_238232 := by
    simpa [prefixWord, tailWord_238232, baseEnd_238232] using wordTrace_append hprefix tailTrace_238232
  have hstable : (prefixWord ++ tailWord_238232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238232).length < 2 ^ (prefixWord ++ tailWord_238232).sum := by decide
  have hdescent : baseEnd_238232 < baseStart_238232 := by decide
  rcases family_descends (prefixWord ++ tailWord_238232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238250 : List Nat := [3, 1, 5, 2, 1, 1, 2, 3, 1, 1, 3]
def baseStart_238250 : Nat := 118140960795 + 238250 * 2 ^ 59
def prefixEnd_238250 : Nat := 4983230072969 + 3 ^ 40 * 238250 * 2
def baseEnd_238250 : Nat := 122336765933798079479315

theorem tailTrace_238250 : CollatzResearch.WordTrace tailWord_238250 prefixEnd_238250 122336765933798079479315 := by
  unfold tailWord_238250
  simp only [CollatzResearch.WordTrace]
  refine ⟨2172422846717103676406051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5793127591245609803749469 2172422846717103676406051)
  ·
    refine ⟨3258634270075655514609077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2172422846717103676406051 3258634270075655514609077)
    ·
      refine ⟨305496962819592704494601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3258634270075655514609077 305496962819592704494601)
      ·
        refine ⟨229122722114694528370951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305496962819592704494601 229122722114694528370951)
        ·
          refine ⟨343684083172041792556427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229122722114694528370951 343684083172041792556427)
          ·
            refine ⟨515526124758062688834641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343684083172041792556427 515526124758062688834641)
            ·
              refine ⟨386644593568547016625981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 515526124758062688834641 386644593568547016625981)
              ·
                refine ⟨144991722588205131234743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 386644593568547016625981 144991722588205131234743)
                ·
                  refine ⟨217487583882307696852115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144991722588205131234743 217487583882307696852115)
                  ·
                    refine ⟨326231375823461545278173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 217487583882307696852115 326231375823461545278173)
                    ·
                      refine ⟨122336765933798079479315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 326231375823461545278173 122336765933798079479315)
                      ·
                        rfl

theorem cell23_238250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_238250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_238250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_238250 prefixEnd_238250 := by exact prefixLift 238250
  have htrace : WordTrace (prefixWord ++ tailWord_238250) baseStart_238250 baseEnd_238250 := by
    simpa [prefixWord, tailWord_238250, baseEnd_238250] using wordTrace_append hprefix tailTrace_238250
  have hstable : (prefixWord ++ tailWord_238250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238250).length < 2 ^ (prefixWord ++ tailWord_238250).sum := by decide
  have hdescent : baseEnd_238250 < baseStart_238250 := by decide
  rcases family_descends (prefixWord ++ tailWord_238250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238259 : List Nat := [1, 1, 1, 2, 3, 4, 4, 1, 1, 2, 3]
def baseStart_238259 : Nat := 118140960795 + 238259 * 2 ^ 59
def prefixEnd_238259 : Nat := 4983230072969 + 3 ^ 40 * 238259 * 2
def baseEnd_238259 : Nat := 122341387259688544266773

theorem tailTrace_238259 : CollatzResearch.WordTrace tailWord_238259 prefixEnd_238259 122341387259688544266773 := by
  unfold tailWord_238259
  simp only [CollatzResearch.WordTrace]
  refine ⟨8690019643835809242701831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5793346429223872828467887 8690019643835809242701831)
  ·
    refine ⟨13035029465753713864052747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8690019643835809242701831 13035029465753713864052747)
    ·
      refine ⟨19552544198630570796079121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13035029465753713864052747 19552544198630570796079121)
      ·
        refine ⟨14664408148972928097059341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19552544198630570796079121 14664408148972928097059341)
        ·
          refine ⟨5499153055864848036397253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14664408148972928097059341 5499153055864848036397253)
          ·
            refine ⟨1031091197974659006824485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5499153055864848036397253 1031091197974659006824485)
            ·
              refine ⟨193329599620248563779591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1031091197974659006824485 193329599620248563779591)
              ·
                refine ⟨289994399430372845669387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193329599620248563779591 289994399430372845669387)
                ·
                  refine ⟨434991599145559268504081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 289994399430372845669387 434991599145559268504081)
                  ·
                    refine ⟨326243699359169451378061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 434991599145559268504081 326243699359169451378061)
                    ·
                      refine ⟨122341387259688544266773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 326243699359169451378061 122341387259688544266773)
                      ·
                        rfl

theorem cell23_238259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 1, 1, 2, 3].length) (baseStart_238259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_238259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_238259 prefixEnd_238259 := by exact prefixLift 238259
  have htrace : WordTrace (prefixWord ++ tailWord_238259) baseStart_238259 baseEnd_238259 := by
    simpa [prefixWord, tailWord_238259, baseEnd_238259] using wordTrace_append hprefix tailTrace_238259
  have hstable : (prefixWord ++ tailWord_238259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238259).length < 2 ^ (prefixWord ++ tailWord_238259).sum := by decide
  have hdescent : baseEnd_238259 < baseStart_238259 := by decide
  rcases family_descends (prefixWord ++ tailWord_238259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238315 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 1, 6, 3]
def baseStart_238315 : Nat := 118140960795 + 238315 * 2 ^ 59
def prefixEnd_238315 : Nat := 4983230072969 + 3 ^ 40 * 238315 * 2
def baseEnd_238315 : Nat := 122370142176340325166515

theorem tailTrace_238315 : CollatzResearch.WordTrace tailWord_238315 prefixEnd_238315 122370142176340325166515 := by
  unfold tailWord_238315
  simp only [CollatzResearch.WordTrace]
  refine ⟨8692062131632930806740399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5794708087755287204493599 8692062131632930806740399)
  ·
    refine ⟨13038093197449396210110599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8692062131632930806740399 13038093197449396210110599)
    ·
      refine ⟨19557139796174094315165899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13038093197449396210110599 19557139796174094315165899)
      ·
        refine ⟨29335709694261141472748849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19557139796174094315165899 29335709694261141472748849)
        ·
          refine ⟨22001782270695856104561637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29335709694261141472748849 22001782270695856104561637)
          ·
            refine ⟨4125334175755473019605307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22001782270695856104561637 4125334175755473019605307)
            ·
              refine ⟨6188001263633209529407961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4125334175755473019605307 6188001263633209529407961)
              ·
                refine ⟨4641000947724907147055971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6188001263633209529407961 4641000947724907147055971)
                ·
                  refine ⟨6961501421587360720583957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4641000947724907147055971 6961501421587360720583957)
                  ·
                    refine ⟨326320379136907533777373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6961501421587360720583957 326320379136907533777373)
                    ·
                      refine ⟨122370142176340325166515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 326320379136907533777373 122370142176340325166515)
                      ·
                        rfl

theorem cell23_238315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 6, 3].length) (baseStart_238315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_238315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_238315 prefixEnd_238315 := by exact prefixLift 238315
  have htrace : WordTrace (prefixWord ++ tailWord_238315) baseStart_238315 baseEnd_238315 := by
    simpa [prefixWord, tailWord_238315, baseEnd_238315] using wordTrace_append hprefix tailTrace_238315
  have hstable : (prefixWord ++ tailWord_238315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238315).length < 2 ^ (prefixWord ++ tailWord_238315).sum := by decide
  have hdescent : baseEnd_238315 < baseStart_238315 := by decide
  rcases family_descends (prefixWord ++ tailWord_238315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238324 : List Nat := [2, 6, 1, 1, 2, 1, 3, 2, 1, 2, 2]
def baseStart_238324 : Nat := 118140960795 + 238324 * 2 ^ 59
def prefixEnd_238324 : Nat := 4983230072969 + 3 ^ 40 * 238324 * 2
def baseEnd_238324 : Nat := 122374763502230789953975

theorem tailTrace_238324 : CollatzResearch.WordTrace tailWord_238324 prefixEnd_238324 122374763502230789953975 := by
  unfold tailWord_238324
  simp only [CollatzResearch.WordTrace]
  refine ⟨4346195194300162671909013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5794926925733550229212017 4346195194300162671909013)
  ·
    refine ⟨203727899732820125245735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4346195194300162671909013 203727899732820125245735)
    ·
      refine ⟨305591849599230187868603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203727899732820125245735 305591849599230187868603)
      ·
        refine ⟨458387774398845281802905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305591849599230187868603 458387774398845281802905)
        ·
          refine ⟨343790830799133961352179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 458387774398845281802905 343790830799133961352179)
          ·
            refine ⟨515686246198700942028269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343790830799133961352179 515686246198700942028269)
            ·
              refine ⟨193382342324512853260601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 515686246198700942028269 193382342324512853260601)
              ·
                refine ⟨145036756743384639945451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193382342324512853260601 145036756743384639945451)
                ·
                  refine ⟨217555135115076959918177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145036756743384639945451 217555135115076959918177)
                  ·
                    refine ⟨163166351336307719938633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 217555135115076959918177 163166351336307719938633)
                    ·
                      refine ⟨122374763502230789953975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 163166351336307719938633 122374763502230789953975)
                      ·
                        rfl

theorem cell23_238324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_238324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_238324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_238324 prefixEnd_238324 := by exact prefixLift 238324
  have htrace : WordTrace (prefixWord ++ tailWord_238324) baseStart_238324 baseEnd_238324 := by
    simpa [prefixWord, tailWord_238324, baseEnd_238324] using wordTrace_append hprefix tailTrace_238324
  have hstable : (prefixWord ++ tailWord_238324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238324).length < 2 ^ (prefixWord ++ tailWord_238324).sum := by decide
  have hdescent : baseEnd_238324 < baseStart_238324 := by decide
  rcases family_descends (prefixWord ++ tailWord_238324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238346 : List Nat := [3, 1, 2, 2, 1, 2, 3, 3, 2, 2, 2]
def baseStart_238346 : Nat := 118140960795 + 238346 * 2 ^ 59
def prefixEnd_238346 : Nat := 4983230072969 + 3 ^ 40 * 238346 * 2
def baseEnd_238346 : Nat := 122386060076629703878873

theorem tailTrace_238346 : CollatzResearch.WordTrace tailWord_238346 prefixEnd_238346 122386060076629703878873 := by
  unfold tailWord_238346
  simp only [CollatzResearch.WordTrace]
  refine ⟨2173298198630155775279723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5795461863013748734079261 2173298198630155775279723)
  ·
    refine ⟨3259947297945233662919585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2173298198630155775279723 3259947297945233662919585)
    ·
      refine ⟨2444960473458925247189689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3259947297945233662919585 2444960473458925247189689)
      ·
        refine ⟨1833720355094193935392267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2444960473458925247189689 1833720355094193935392267)
        ·
          refine ⟨2750580532641290903088401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1833720355094193935392267 2750580532641290903088401)
          ·
            refine ⟨2062935399480968177316301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2750580532641290903088401 2062935399480968177316301)
            ·
              refine ⟨773600774805363066493613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2062935399480968177316301 773600774805363066493613)
              ·
                refine ⟨290100290552011149935105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 773600774805363066493613 290100290552011149935105)
                ·
                  refine ⟨217575217914008362451329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 290100290552011149935105 217575217914008362451329)
                  ·
                    refine ⟨163181413435506271838497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 217575217914008362451329 163181413435506271838497)
                    ·
                      refine ⟨122386060076629703878873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 163181413435506271838497 122386060076629703878873)
                      ·
                        rfl

theorem cell23_238346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3, 2, 2, 2].length) (baseStart_238346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_238346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_238346 prefixEnd_238346 := by exact prefixLift 238346
  have htrace : WordTrace (prefixWord ++ tailWord_238346) baseStart_238346 baseEnd_238346 := by
    simpa [prefixWord, tailWord_238346, baseEnd_238346] using wordTrace_append hprefix tailTrace_238346
  have hstable : (prefixWord ++ tailWord_238346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238346).length < 2 ^ (prefixWord ++ tailWord_238346).sum := by decide
  have hdescent : baseEnd_238346 < baseStart_238346 := by decide
  rcases family_descends (prefixWord ++ tailWord_238346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238389 : List Nat := [1, 3, 3, 1, 3, 1, 1, 1, 2, 5, 2]
def baseStart_238389 : Nat := 118140960795 + 238389 * 2 ^ 59
def prefixEnd_238389 : Nat := 4983230072969 + 3 ^ 40 * 238389 * 2
def baseEnd_238389 : Nat := 122408139744773035641175

theorem tailTrace_238389 : CollatzResearch.WordTrace tailWord_238389 prefixEnd_238389 122408139744773035641175 := by
  unfold tailWord_238389
  simp only [CollatzResearch.WordTrace]
  refine ⟨8694761133364841444934221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5796507422243227629956147 8694761133364841444934221)
  ·
    refine ⟨3260535425011815541850333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8694761133364841444934221 3260535425011815541850333)
    ·
      refine ⟨1222700784379430828193875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3260535425011815541850333 1222700784379430828193875)
      ·
        refine ⟨1834051176569146242290813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1222700784379430828193875 1834051176569146242290813)
        ·
          refine ⟨687769191213429840859055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1834051176569146242290813 687769191213429840859055)
          ·
            refine ⟨1031653786820144761288583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 687769191213429840859055 1031653786820144761288583)
            ·
              refine ⟨1547480680230217141932875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1031653786820144761288583 1547480680230217141932875)
              ·
                refine ⟨2321221020345325712899313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1547480680230217141932875 2321221020345325712899313)
                ·
                  refine ⟨1740915765258994284674485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2321221020345325712899313 1740915765258994284674485)
                  ·
                    refine ⟨163210852993030714188233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1740915765258994284674485 163210852993030714188233)
                    ·
                      refine ⟨122408139744773035641175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 163210852993030714188233 122408139744773035641175)
                      ·
                        rfl

theorem cell23_238389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 5, 2].length) (baseStart_238389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_238389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_238389 prefixEnd_238389 := by exact prefixLift 238389
  have htrace : WordTrace (prefixWord ++ tailWord_238389) baseStart_238389 baseEnd_238389 := by
    simpa [prefixWord, tailWord_238389, baseEnd_238389] using wordTrace_append hprefix tailTrace_238389
  have hstable : (prefixWord ++ tailWord_238389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238389).length < 2 ^ (prefixWord ++ tailWord_238389).sum := by decide
  have hdescent : baseEnd_238389 < baseStart_238389 := by decide
  rcases family_descends (prefixWord ++ tailWord_238389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238415 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 6]
def baseStart_238415 : Nat := 118140960795 + 238415 * 2 ^ 59
def prefixEnd_238415 : Nat := 4983230072969 + 3 ^ 40 * 238415 * 2
def baseEnd_238415 : Nat := 122421490241789933916055

theorem tailTrace_238415 : CollatzResearch.WordTrace tailWord_238415 prefixEnd_238415 122421490241789933916055 := by
  unfold tailWord_238415
  simp only [CollatzResearch.WordTrace]
  refine ⟨8695709431270647885380699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5797139620847098590253799 8695709431270647885380699)
  ·
    refine ⟨13043564146905971828071049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8695709431270647885380699 13043564146905971828071049)
    ·
      refine ⟨9782673110179478871053287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13043564146905971828071049 9782673110179478871053287)
      ·
        refine ⟨14674009665269218306579931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9782673110179478871053287 14674009665269218306579931)
        ·
          refine ⟨22011014497903827459869897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14674009665269218306579931 22011014497903827459869897)
          ·
            refine ⟨16508260873427870594902423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22011014497903827459869897 16508260873427870594902423)
            ·
              refine ⟨24762391310141805892353635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16508260873427870594902423 24762391310141805892353635)
              ·
                refine ⟨37143586965212708838530453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24762391310141805892353635 37143586965212708838530453)
                ·
                  refine ⟨1741105638994345726806115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 37143586965212708838530453 1741105638994345726806115)
                  ·
                    refine ⟨2611658458491518590209173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1741105638994345726806115 2611658458491518590209173)
                    ·
                      refine ⟨122421490241789933916055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2611658458491518590209173 122421490241789933916055)
                      ·
                        rfl

theorem cell23_238415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 6].length) (baseStart_238415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_238415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_238415 prefixEnd_238415 := by exact prefixLift 238415
  have htrace : WordTrace (prefixWord ++ tailWord_238415) baseStart_238415 baseEnd_238415 := by
    simpa [prefixWord, tailWord_238415, baseEnd_238415] using wordTrace_append hprefix tailTrace_238415
  have hstable : (prefixWord ++ tailWord_238415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238415).length < 2 ^ (prefixWord ++ tailWord_238415).sum := by decide
  have hdescent : baseEnd_238415 < baseStart_238415 := by decide
  rcases family_descends (prefixWord ++ tailWord_238415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238522 : List Nat := [3, 1, 1, 1, 2, 1, 3, 3, 1, 1, 6]
def baseStart_238522 : Nat := 118140960795 + 238522 * 2 ^ 59
def prefixEnd_238522 : Nat := 4983230072969 + 3 ^ 40 * 238522 * 2
def baseEnd_238522 : Nat := 122476432671821015278063

theorem tailTrace_238522 : CollatzResearch.WordTrace tailWord_238522 prefixEnd_238522 122476432671821015278063 := by
  unfold tailWord_238522
  simp only [CollatzResearch.WordTrace]
  refine ⟨2174903010470751289881455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5799741361255336773017213 2174903010470751289881455)
  ·
    refine ⟨3262354515706126934822183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2174903010470751289881455 3262354515706126934822183)
    ·
      refine ⟨4893531773559190402233275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3262354515706126934822183 4893531773559190402233275)
      ·
        refine ⟨7340297660338785603349913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4893531773559190402233275 7340297660338785603349913)
        ·
          refine ⟨5505223245254089202512435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7340297660338785603349913 5505223245254089202512435)
          ·
            refine ⟨8257834867881133803768653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5505223245254089202512435 8257834867881133803768653)
            ·
              refine ⟨3096688075455425176413245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8257834867881133803768653 3096688075455425176413245)
              ·
                refine ⟨1161258028295784441154967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3096688075455425176413245 1161258028295784441154967)
                ·
                  refine ⟨1741887042443676661732451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1161258028295784441154967 1741887042443676661732451)
                  ·
                    refine ⟨2612830563665514992598677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1741887042443676661732451 2612830563665514992598677)
                    ·
                      refine ⟨122476432671821015278063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2612830563665514992598677 122476432671821015278063)
                      ·
                        rfl

theorem cell23_238522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 1, 1, 6].length) (baseStart_238522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_238522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_238522 prefixEnd_238522 := by exact prefixLift 238522
  have htrace : WordTrace (prefixWord ++ tailWord_238522) baseStart_238522 baseEnd_238522 := by
    simpa [prefixWord, tailWord_238522, baseEnd_238522] using wordTrace_append hprefix tailTrace_238522
  have hstable : (prefixWord ++ tailWord_238522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238522).length < 2 ^ (prefixWord ++ tailWord_238522).sum := by decide
  have hdescent : baseEnd_238522 < baseStart_238522 := by decide
  rcases family_descends (prefixWord ++ tailWord_238522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238539 : List Nat := [1, 1, 1, 1, 3, 6, 1, 2, 1, 2, 4]
def baseStart_238539 : Nat := 118140960795 + 238539 * 2 ^ 59
def prefixEnd_238539 : Nat := 4983230072969 + 3 ^ 40 * 238539 * 2
def baseEnd_238539 : Nat := 122485161842947448765485

theorem tailTrace_238539 : CollatzResearch.WordTrace tailWord_238539 prefixEnd_238539 122485161842947448765485 := by
  unfold tailWord_238539
  simp only [CollatzResearch.WordTrace]
  refine ⟨8700232082821417062894671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5800154721880944708596447 8700232082821417062894671)
  ·
    refine ⟨13050348124232125594342007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8700232082821417062894671 13050348124232125594342007)
    ·
      refine ⟨19575522186348188391513011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13050348124232125594342007 19575522186348188391513011)
      ·
        refine ⟨29363283279522282587269517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19575522186348188391513011 29363283279522282587269517)
        ·
          refine ⟨11011231229820855970226069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29363283279522282587269517 11011231229820855970226069)
          ·
            refine ⟨516151463897852623604347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11011231229820855970226069 516151463897852623604347)
            ·
              refine ⟨774227195846778935406521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 516151463897852623604347 774227195846778935406521)
              ·
                refine ⟨580670396885084201554891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 774227195846778935406521 580670396885084201554891)
                ·
                  refine ⟨871005595327626302332337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 580670396885084201554891 871005595327626302332337)
                  ·
                    refine ⟨653254196495719726749253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 871005595327626302332337 653254196495719726749253)
                    ·
                      refine ⟨122485161842947448765485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 653254196495719726749253 122485161842947448765485)
                      ·
                        rfl

theorem cell23_238539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 2, 4].length) (baseStart_238539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_238539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_238539 prefixEnd_238539 := by exact prefixLift 238539
  have htrace : WordTrace (prefixWord ++ tailWord_238539) baseStart_238539 baseEnd_238539 := by
    simpa [prefixWord, tailWord_238539, baseEnd_238539] using wordTrace_append hprefix tailTrace_238539
  have hstable : (prefixWord ++ tailWord_238539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238539).length < 2 ^ (prefixWord ++ tailWord_238539).sum := by decide
  have hdescent : baseEnd_238539 < baseStart_238539 := by decide
  rcases family_descends (prefixWord ++ tailWord_238539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238546 : List Nat := [3, 2, 2, 3, 1, 1, 3, 1, 1, 1, 5]
def baseStart_238546 : Nat := 118140960795 + 238546 * 2 ^ 59
def prefixEnd_238546 : Nat := 4983230072969 + 3 ^ 40 * 238546 * 2
def baseEnd_238546 : Nat := 122488756207528921377953

theorem tailTrace_238546 : CollatzResearch.WordTrace tailWord_238546 prefixEnd_238546 122488756207528921377953 := by
  unfold tailWord_238546
  simp only [CollatzResearch.WordTrace]
  refine ⟨2175121848449014314599873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5800324929197371505599661 2175121848449014314599873)
  ·
    refine ⟨1631341386336760735949905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2175121848449014314599873 1631341386336760735949905)
    ·
      refine ⟨1223506039752570551962429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1631341386336760735949905 1223506039752570551962429)
      ·
        refine ⟨458814764907213956985911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1223506039752570551962429 458814764907213956985911)
        ·
          refine ⟨688222147360820935478867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458814764907213956985911 688222147360820935478867)
          ·
            refine ⟨1032333221041231403218301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 688222147360820935478867 1032333221041231403218301)
            ·
              refine ⟨387124957890461776206863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1032333221041231403218301 387124957890461776206863)
              ·
                refine ⟨580687436835692664310295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 387124957890461776206863 580687436835692664310295)
                ·
                  refine ⟨871031155253538996465443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 580687436835692664310295 871031155253538996465443)
                  ·
                    refine ⟨1306546732880308494698165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 871031155253538996465443 1306546732880308494698165)
                    ·
                      refine ⟨122488756207528921377953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1306546732880308494698165 122488756207528921377953)
                      ·
                        rfl

theorem cell23_238546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_238546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_238546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_238546 prefixEnd_238546 := by exact prefixLift 238546
  have htrace : WordTrace (prefixWord ++ tailWord_238546) baseStart_238546 baseEnd_238546 := by
    simpa [prefixWord, tailWord_238546, baseEnd_238546] using wordTrace_append hprefix tailTrace_238546
  have hstable : (prefixWord ++ tailWord_238546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238546).length < 2 ^ (prefixWord ++ tailWord_238546).sum := by decide
  have hdescent : baseEnd_238546 < baseStart_238546 := by decide
  rcases family_descends (prefixWord ++ tailWord_238546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238549 : List Nat := [1, 3, 2, 3, 4, 10]
def baseStart_238549 : Nat := 118140960795 + 238549 * 2 ^ 59
def prefixEnd_238549 : Nat := 4983230072969 + 3 ^ 40 * 238549 * 2
def baseEnd_238549 : Nat := 504075294853878228973

theorem tailTrace_238549 : CollatzResearch.WordTrace tailWord_238549 prefixEnd_238549 504075294853878228973 := by
  unfold tailWord_238549
  simp only [CollatzResearch.WordTrace]
  refine ⟨8700596812785188770758701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5800397875190125847172467 8700596812785188770758701)
  ·
    refine ⟨3262723804794445789034513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8700596812785188770758701 3262723804794445789034513)
    ·
      refine ⟨2447042853595834341775885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3262723804794445789034513 2447042853595834341775885)
      ·
        refine ⟨917641070098437878165957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2447042853595834341775885 917641070098437878165957)
        ·
          refine ⟨172057700643457102156117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 917641070098437878165957 172057700643457102156117)
          ·
            refine ⟨504075294853878228973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 172057700643457102156117 504075294853878228973)
            ·
              rfl

theorem cell23_238549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 10].length) (baseStart_238549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_238549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_238549 prefixEnd_238549 := by exact prefixLift 238549
  have htrace : WordTrace (prefixWord ++ tailWord_238549) baseStart_238549 baseEnd_238549 := by
    simpa [prefixWord, tailWord_238549, baseEnd_238549] using wordTrace_append hprefix tailTrace_238549
  have hstable : (prefixWord ++ tailWord_238549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238549).length < 2 ^ (prefixWord ++ tailWord_238549).sum := by decide
  have hdescent : baseEnd_238549 < baseStart_238549 := by decide
  rcases family_descends (prefixWord ++ tailWord_238549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238572 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 5]
def baseStart_238572 : Nat := 118140960795 + 238572 * 2 ^ 59
def prefixEnd_238572 : Nat := 4983230072969 + 3 ^ 40 * 238572 * 2
def baseEnd_238572 : Nat := 122502106704545819652833

theorem tailTrace_238572 : CollatzResearch.WordTrace tailWord_238572 prefixEnd_238572 122502106704545819652833 := by
  unfold tailWord_238572
  simp only [CollatzResearch.WordTrace]
  refine ⟨4350717845850931849422985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5800957127801242465897313 4350717845850931849422985)
  ·
    refine ⟨3263038384388198887067239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4350717845850931849422985 3263038384388198887067239)
    ·
      refine ⟨4894557576582298330600859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3263038384388198887067239 4894557576582298330600859)
      ·
        refine ⟨7341836364873447495901289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4894557576582298330600859 7341836364873447495901289)
        ·
          refine ⟨5506377273655085621925967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7341836364873447495901289 5506377273655085621925967)
          ·
            refine ⟨8259565910482628432888951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5506377273655085621925967 8259565910482628432888951)
            ·
              refine ⟨12389348865723942649333427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8259565910482628432888951 12389348865723942649333427)
              ·
                refine ⟨18584023298585913974000141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12389348865723942649333427 18584023298585913974000141)
                ·
                  refine ⟨6969008736969717740250053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18584023298585913974000141 6969008736969717740250053)
                  ·
                    refine ⟨1306689138181822076296885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6969008736969717740250053 1306689138181822076296885)
                    ·
                      refine ⟨122502106704545819652833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1306689138181822076296885 122502106704545819652833)
                      ·
                        rfl

theorem cell23_238572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_238572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_238572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_238572 prefixEnd_238572 := by exact prefixLift 238572
  have htrace : WordTrace (prefixWord ++ tailWord_238572) baseStart_238572 baseEnd_238572 := by
    simpa [prefixWord, tailWord_238572, baseEnd_238572] using wordTrace_append hprefix tailTrace_238572
  have hstable : (prefixWord ++ tailWord_238572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238572).length < 2 ^ (prefixWord ++ tailWord_238572).sum := by decide
  have hdescent : baseEnd_238572 < baseStart_238572 := by decide
  rcases family_descends (prefixWord ++ tailWord_238572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238594 : List Nat := [3, 4, 1, 3, 2, 1, 2, 1, 1, 1, 4]
def baseStart_238594 : Nat := 118140960795 + 238594 * 2 ^ 59
def prefixEnd_238594 : Nat := 4983230072969 + 3 ^ 40 * 238594 * 2
def baseEnd_238594 : Nat := 122513403278944733577733

theorem tailTrace_238594 : CollatzResearch.WordTrace tailWord_238594 prefixEnd_238594 122513403278944733577733 := by
  unfold tailWord_238594
  simp only [CollatzResearch.WordTrace]
  refine ⟨2175559524405540364036709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5801492065081440970764557 2175559524405540364036709)
  ·
    refine ⟨407917410826038818256883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2175559524405540364036709 407917410826038818256883)
    ·
      refine ⟨611876116239058227385325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407917410826038818256883 611876116239058227385325)
      ·
        refine ⟨229453543589646835269497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 611876116239058227385325 229453543589646835269497)
        ·
          refine ⟨172090157692235126452123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229453543589646835269497 172090157692235126452123)
          ·
            refine ⟨258135236538352689678185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172090157692235126452123 258135236538352689678185)
            ·
              refine ⟨193601427403764517258639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258135236538352689678185 193601427403764517258639)
              ·
                refine ⟨290402141105646775887959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193601427403764517258639 290402141105646775887959)
                ·
                  refine ⟨435603211658470163831939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 290402141105646775887959 435603211658470163831939)
                  ·
                    refine ⟨653404817487705245747909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 435603211658470163831939 653404817487705245747909)
                    ·
                      refine ⟨122513403278944733577733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 653404817487705245747909 122513403278944733577733)
                      ·
                        rfl

theorem cell23_238594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_238594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_238594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_238594 prefixEnd_238594 := by exact prefixLift 238594
  have htrace : WordTrace (prefixWord ++ tailWord_238594) baseStart_238594 baseEnd_238594 := by
    simpa [prefixWord, tailWord_238594, baseEnd_238594] using wordTrace_append hprefix tailTrace_238594
  have hstable : (prefixWord ++ tailWord_238594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238594).length < 2 ^ (prefixWord ++ tailWord_238594).sum := by decide
  have hdescent : baseEnd_238594 < baseStart_238594 := by decide
  rcases family_descends (prefixWord ++ tailWord_238594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238603 : List Nat := [1, 1, 1, 1, 6, 3, 1, 3, 1, 3, 2]
def baseStart_238603 : Nat := 118140960795 + 238603 * 2 ^ 59
def prefixEnd_238603 : Nat := 4983230072969 + 3 ^ 40 * 238603 * 2
def baseEnd_238603 : Nat := 122518024604835198365191

theorem tailTrace_238603 : CollatzResearch.WordTrace tailWord_238603 prefixEnd_238603 122518024604835198365191 := by
  unfold tailWord_238603
  simp only [CollatzResearch.WordTrace]
  refine ⟨8702566354589555993224463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5801710903059703995482975 8702566354589555993224463)
  ·
    refine ⟨13053849531884333989836695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8702566354589555993224463 13053849531884333989836695)
    ·
      refine ⟨19580774297826500984755043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13053849531884333989836695 19580774297826500984755043)
      ·
        refine ⟨29371161446739751477132565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19580774297826500984755043 29371161446739751477132565)
        ·
          refine ⟨1376773192815925850490589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29371161446739751477132565 1376773192815925850490589)
          ·
            refine ⟨516289947305972193933971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1376773192815925850490589 516289947305972193933971)
            ·
              refine ⟨774434920958958290900957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 516289947305972193933971 774434920958958290900957)
              ·
                refine ⟨290413095359609359087859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 774434920958958290900957 290413095359609359087859)
                ·
                  refine ⟨435619643039414038631789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 290413095359609359087859 435619643039414038631789)
                  ·
                    refine ⟨163357366139780264486921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 435619643039414038631789 163357366139780264486921)
                    ·
                      refine ⟨122518024604835198365191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 163357366139780264486921 122518024604835198365191)
                      ·
                        rfl

theorem cell23_238603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3, 1, 3, 2].length) (baseStart_238603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_238603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_238603 prefixEnd_238603 := by exact prefixLift 238603
  have htrace : WordTrace (prefixWord ++ tailWord_238603) baseStart_238603 baseEnd_238603 := by
    simpa [prefixWord, tailWord_238603, baseEnd_238603] using wordTrace_append hprefix tailTrace_238603
  have hstable : (prefixWord ++ tailWord_238603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238603).length < 2 ^ (prefixWord ++ tailWord_238603).sum := by decide
  have hdescent : baseEnd_238603 < baseStart_238603 := by decide
  rcases family_descends (prefixWord ++ tailWord_238603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238629 : List Nat := [1, 3, 1, 2, 2, 2, 1, 3, 2, 2, 4]
def baseStart_238629 : Nat := 118140960795 + 238629 * 2 ^ 59
def prefixEnd_238629 : Nat := 4983230072969 + 3 ^ 40 * 238629 * 2
def baseEnd_238629 : Nat := 122531375101852096640071

theorem tailTrace_238629 : CollatzResearch.WordTrace tailWord_238629 prefixEnd_238629 122531375101852096640071 := by
  unfold tailWord_238629
  simp only [CollatzResearch.WordTrace]
  refine ⟨8703514652495362433670941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5802343101663574955780627 8703514652495362433670941)
  ·
    refine ⟨3263817994685760912626603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8703514652495362433670941 3263817994685760912626603)
    ·
      refine ⟨4895726992028641368939905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3263817994685760912626603 4895726992028641368939905)
      ·
        refine ⟨3671795244021481026704929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4895726992028641368939905 3671795244021481026704929)
        ·
          refine ⟨2753846433016110770028697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3671795244021481026704929 2753846433016110770028697)
          ·
            refine ⟨2065384824762083077521523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2753846433016110770028697 2065384824762083077521523)
            ·
              refine ⟨3098077237143124616282285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2065384824762083077521523 3098077237143124616282285)
              ·
                refine ⟨1161778963928671731105857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3098077237143124616282285 1161778963928671731105857)
                ·
                  refine ⟨871334222946503798329393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1161778963928671731105857 871334222946503798329393)
                  ·
                    refine ⟨653500667209877848747045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 871334222946503798329393 653500667209877848747045)
                    ·
                      refine ⟨122531375101852096640071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 653500667209877848747045 122531375101852096640071)
                      ·
                        rfl

theorem cell23_238629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_238629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_238629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_238629 prefixEnd_238629 := by exact prefixLift 238629
  have htrace : WordTrace (prefixWord ++ tailWord_238629) baseStart_238629 baseEnd_238629 := by
    simpa [prefixWord, tailWord_238629, baseEnd_238629] using wordTrace_append hprefix tailTrace_238629
  have hstable : (prefixWord ++ tailWord_238629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238629).length < 2 ^ (prefixWord ++ tailWord_238629).sum := by decide
  have hdescent : baseEnd_238629 < baseStart_238629 := by decide
  rcases family_descends (prefixWord ++ tailWord_238629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238689 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 3, 3, 4]
def baseStart_238689 : Nat := 118140960795 + 238689 * 2 ^ 59
def prefixEnd_238689 : Nat := 4983230072969 + 3 ^ 40 * 238689 * 2
def baseEnd_238689 : Nat := 122562183941121861889795

theorem tailTrace_238689 : CollatzResearch.WordTrace tailWord_238689 prefixEnd_238689 122562183941121861889795 := by
  unfold tailWord_238689
  simp only [CollatzResearch.WordTrace]
  refine ⟨8705703032277992680855121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5803802021518661787236747 8705703032277992680855121)
  ·
    refine ⟨6529277274208494510641341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8705703032277992680855121 6529277274208494510641341)
    ·
      refine ⟨2448478977828185441490503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6529277274208494510641341 2448478977828185441490503)
      ·
        refine ⟨3672718466742278162235755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2448478977828185441490503 3672718466742278162235755)
        ·
          refine ⟨5509077700113417243353633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3672718466742278162235755 5509077700113417243353633)
          ·
            refine ⟨4131808275085062932515225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5509077700113417243353633 4131808275085062932515225)
            ·
              refine ⟨3098856206313797199386419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4131808275085062932515225 3098856206313797199386419)
              ·
                refine ⟨4648284309470695799079629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3098856206313797199386419 4648284309470695799079629)
                ·
                  refine ⟨1743106616051510924654861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4648284309470695799079629 1743106616051510924654861)
                  ·
                    refine ⟨653664981019316596745573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1743106616051510924654861 653664981019316596745573)
                    ·
                      refine ⟨122562183941121861889795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 653664981019316596745573 122562183941121861889795)
                      ·
                        rfl

theorem cell23_238689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_238689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_238689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_238689 prefixEnd_238689 := by exact prefixLift 238689
  have htrace : WordTrace (prefixWord ++ tailWord_238689) baseStart_238689 baseEnd_238689 := by
    simpa [prefixWord, tailWord_238689, baseEnd_238689] using wordTrace_append hprefix tailTrace_238689
  have hstable : (prefixWord ++ tailWord_238689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238689).length < 2 ^ (prefixWord ++ tailWord_238689).sum := by decide
  have hdescent : baseEnd_238689 < baseStart_238689 := by decide
  rcases family_descends (prefixWord ++ tailWord_238689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238750 : List Nat := [4, 3, 1, 1, 2, 2, 1, 2, 3, 4]
def baseStart_238750 : Nat := 118140960795 + 238750 * 2 ^ 59
def prefixEnd_238750 : Nat := 4983230072969 + 3 ^ 40 * 238750 * 2
def baseEnd_238750 : Nat := 40864502087015374409005

theorem tailTrace_238750 : CollatzResearch.WordTrace tailWord_238750 prefixEnd_238750 40864502087015374409005 := by
  unfold tailWord_238750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1088490985632125012353213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5805285256704666732550469 1088490985632125012353213)
  ·
    refine ⟨408184119612046879632455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1088490985632125012353213 408184119612046879632455)
    ·
      refine ⟨612276179418070319448683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408184119612046879632455 612276179418070319448683)
      ·
        refine ⟨918414269127105479173025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 612276179418070319448683 918414269127105479173025)
        ·
          refine ⟨688810701845329109379769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 918414269127105479173025 688810701845329109379769)
          ·
            refine ⟨516608026383996832034827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 688810701845329109379769 516608026383996832034827)
            ·
              refine ⟨774912039575995248052241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 516608026383996832034827 774912039575995248052241)
              ·
                refine ⟨581184029681996436039181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 774912039575995248052241 581184029681996436039181)
                ·
                  refine ⟨217944011130748663514693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 581184029681996436039181 217944011130748663514693)
                  ·
                    refine ⟨40864502087015374409005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 217944011130748663514693 40864502087015374409005)
                    ·
                      rfl

theorem cell23_238750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_238750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_238750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_238750 prefixEnd_238750 := by exact prefixLift 238750
  have htrace : WordTrace (prefixWord ++ tailWord_238750) baseStart_238750 baseEnd_238750 := by
    simpa [prefixWord, tailWord_238750, baseEnd_238750] using wordTrace_append hprefix tailTrace_238750
  have hstable : (prefixWord ++ tailWord_238750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238750).length < 2 ^ (prefixWord ++ tailWord_238750).sum := by decide
  have hdescent : baseEnd_238750 < baseStart_238750 := by decide
  rcases family_descends (prefixWord ++ tailWord_238750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238783 : List Nat := [1, 1, 2, 2, 2, 2, 2, 4, 2, 3, 2]
def baseStart_238783 : Nat := 118140960795 + 238783 * 2 ^ 59
def prefixEnd_238783 : Nat := 4983230072969 + 3 ^ 40 * 238783 * 2
def baseEnd_238783 : Nat := 122610451122644494114363

theorem tailTrace_238783 : CollatzResearch.WordTrace tailWord_238783 prefixEnd_238783 122610451122644494114363 := by
  unfold tailWord_238783
  simp only [CollatzResearch.WordTrace]
  refine ⟨8709131493937446734777003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5806087662624964489851335 8709131493937446734777003)
  ·
    refine ⟨13063697240906170102165505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8709131493937446734777003 13063697240906170102165505)
    ·
      refine ⟨9797772930679627576624129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13063697240906170102165505 9797772930679627576624129)
      ·
        refine ⟨7348329698009720682468097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9797772930679627576624129 7348329698009720682468097)
        ·
          refine ⟨5511247273507290511851073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7348329698009720682468097 5511247273507290511851073)
          ·
            refine ⟨4133435455130467883888305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5511247273507290511851073 4133435455130467883888305)
            ·
              refine ⟨3100076591347850912916229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4133435455130467883888305 3100076591347850912916229)
              ·
                refine ⟨581264360877722046171793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3100076591347850912916229 581264360877722046171793)
                ·
                  refine ⟨435948270658291534628845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 581264360877722046171793 435948270658291534628845)
                  ·
                    refine ⟨163480601496859325485817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 435948270658291534628845 163480601496859325485817)
                    ·
                      refine ⟨122610451122644494114363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 163480601496859325485817 122610451122644494114363)
                      ·
                        rfl

theorem cell23_238783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2, 3, 2].length) (baseStart_238783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_238783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_238783 prefixEnd_238783 := by exact prefixLift 238783
  have htrace : WordTrace (prefixWord ++ tailWord_238783) baseStart_238783 baseEnd_238783 := by
    simpa [prefixWord, tailWord_238783, baseEnd_238783] using wordTrace_append hprefix tailTrace_238783
  have hstable : (prefixWord ++ tailWord_238783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238783).length < 2 ^ (prefixWord ++ tailWord_238783).sum := by decide
  have hdescent : baseEnd_238783 < baseStart_238783 := by decide
  rcases family_descends (prefixWord ++ tailWord_238783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238830 : List Nat := [4, 1, 2, 1, 1, 1, 2, 2, 5, 2, 2]
def baseStart_238830 : Nat := 118140960795 + 238830 * 2 ^ 59
def prefixEnd_238830 : Nat := 4983230072969 + 3 ^ 40 * 238830 * 2
def baseEnd_238830 : Nat := 122634584713405810226647

theorem tailTrace_238830 : CollatzResearch.WordTrace tailWord_238830 prefixEnd_238830 122634584713405810226647 := by
  unfold tailWord_238830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1088855715595896720217243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5807230483178115841158629 1088855715595896720217243)
  ·
    refine ⟨1633283573393845080325865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1088855715595896720217243 1633283573393845080325865)
    ·
      refine ⟨1224962680045383810244399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1633283573393845080325865 1224962680045383810244399)
      ·
        refine ⟨1837444020068075715366599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1224962680045383810244399 1837444020068075715366599)
        ·
          refine ⟨2756166030102113573049899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1837444020068075715366599 2756166030102113573049899)
          ·
            refine ⟨4134249045153170359574849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2756166030102113573049899 4134249045153170359574849)
            ·
              refine ⟨3100686783864877769681137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4134249045153170359574849 3100686783864877769681137)
              ·
                refine ⟨2325515087898658327260853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3100686783864877769681137 2325515087898658327260853)
                ·
                  refine ⟨218017039490499218180705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2325515087898658327260853 218017039490499218180705)
                  ·
                    refine ⟨163512779617874413635529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 218017039490499218180705 163512779617874413635529)
                    ·
                      refine ⟨122634584713405810226647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 163512779617874413635529 122634584713405810226647)
                      ·
                        rfl

theorem cell23_238830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 5, 2, 2].length) (baseStart_238830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_238830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_238830 prefixEnd_238830 := by exact prefixLift 238830
  have htrace : WordTrace (prefixWord ++ tailWord_238830) baseStart_238830 baseEnd_238830 := by
    simpa [prefixWord, tailWord_238830, baseEnd_238830] using wordTrace_append hprefix tailTrace_238830
  have hstable : (prefixWord ++ tailWord_238830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238830).length < 2 ^ (prefixWord ++ tailWord_238830).sum := by decide
  have hdescent : baseEnd_238830 < baseStart_238830 := by decide
  rcases family_descends (prefixWord ++ tailWord_238830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238847 : List Nat := [1, 1, 2, 2, 1, 7, 1, 1, 3, 2, 2]
def baseStart_238847 : Nat := 118140960795 + 238847 * 2 ^ 59
def prefixEnd_238847 : Nat := 4983230072969 + 3 ^ 40 * 238847 * 2
def baseEnd_238847 : Nat := 122643313884532243714069

theorem tailTrace_238847 : CollatzResearch.WordTrace tailWord_238847 prefixEnd_238847 122643313884532243714069 := by
  unfold tailWord_238847
  simp only [CollatzResearch.WordTrace]
  refine ⟨8711465765705585665106795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5807643843803723776737863 8711465765705585665106795)
  ·
    refine ⟨13067198648558378497660193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8711465765705585665106795 13067198648558378497660193)
    ·
      refine ⟨9800398986418783873245145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13067198648558378497660193 9800398986418783873245145)
      ·
        refine ⟨7350299239814087904933859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9800398986418783873245145 7350299239814087904933859)
        ·
          refine ⟨11025448859721131857400789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7350299239814087904933859 11025448859721131857400789)
          ·
            refine ⟨258408957649714027907831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 11025448859721131857400789 258408957649714027907831)
            ·
              refine ⟨387613436474571041861747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258408957649714027907831 387613436474571041861747)
              ·
                refine ⟨581420154711856562792621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 387613436474571041861747 581420154711856562792621)
                ·
                  refine ⟨218032558016946211047233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 581420154711856562792621 218032558016946211047233)
                  ·
                    refine ⟨163524418512709658285425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 218032558016946211047233 163524418512709658285425)
                    ·
                      refine ⟨122643313884532243714069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 163524418512709658285425 122643313884532243714069)
                      ·
                        rfl

theorem cell23_238847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 3, 2, 2].length) (baseStart_238847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_238847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_238847 prefixEnd_238847 := by exact prefixLift 238847
  have htrace : WordTrace (prefixWord ++ tailWord_238847) baseStart_238847 baseEnd_238847 := by
    simpa [prefixWord, tailWord_238847, baseEnd_238847] using wordTrace_append hprefix tailTrace_238847
  have hstable : (prefixWord ++ tailWord_238847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238847).length < 2 ^ (prefixWord ++ tailWord_238847).sum := by decide
  have hdescent : baseEnd_238847 < baseStart_238847 := by decide
  rcases family_descends (prefixWord ++ tailWord_238847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238876 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 1, 4, 5]
def baseStart_238876 : Nat := 118140960795 + 238876 * 2 ^ 59
def prefixEnd_238876 : Nat := 4983230072969 + 3 ^ 40 * 238876 * 2
def baseEnd_238876 : Nat := 122658204823512630251435

theorem tailTrace_238876 : CollatzResearch.WordTrace tailWord_238876 prefixEnd_238876 122658204823512630251435 := by
  unfold tailWord_238876
  simp only [CollatzResearch.WordTrace]
  refine ⟨4356261741300261808956241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5808348988400349078608321 4356261741300261808956241)
  ·
    refine ⟨3267196305975196356717181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4356261741300261808956241 3267196305975196356717181)
    ·
      refine ⟨1225198614740698633768943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3267196305975196356717181 1225198614740698633768943)
      ·
        refine ⟨1837797922111047950653415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1225198614740698633768943 1837797922111047950653415)
        ·
          refine ⟨2756696883166571925980123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1837797922111047950653415 2756696883166571925980123)
          ·
            refine ⟨4135045324749857888970185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2756696883166571925980123 4135045324749857888970185)
            ·
              refine ⟨3101283993562393416727639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4135045324749857888970185 3101283993562393416727639)
              ·
                refine ⟨4651925990343590125091459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3101283993562393416727639 4651925990343590125091459)
                ·
                  refine ⟨6977888985515385187637189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4651925990343590125091459 6977888985515385187637189)
                  ·
                    refine ⟨1308354184784134722681973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6977888985515385187637189 1308354184784134722681973)
                    ·
                      refine ⟨122658204823512630251435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1308354184784134722681973 122658204823512630251435)
                      ·
                        rfl

theorem cell23_238876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_238876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_238876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_238876 prefixEnd_238876 := by exact prefixLift 238876
  have htrace : WordTrace (prefixWord ++ tailWord_238876) baseStart_238876 baseEnd_238876 := by
    simpa [prefixWord, tailWord_238876, baseEnd_238876] using wordTrace_append hprefix tailTrace_238876
  have hstable : (prefixWord ++ tailWord_238876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238876).length < 2 ^ (prefixWord ++ tailWord_238876).sum := by decide
  have hdescent : baseEnd_238876 < baseStart_238876 := by decide
  rcases family_descends (prefixWord ++ tailWord_238876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238880 : List Nat := [2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 3]
def baseStart_238880 : Nat := 118140960795 + 238880 * 2 ^ 59
def prefixEnd_238880 : Nat := 4983230072969 + 3 ^ 40 * 238880 * 2
def baseEnd_238880 : Nat := 122660258746130614601417

theorem tailTrace_238880 : CollatzResearch.WordTrace tailWord_238880 prefixEnd_238880 122660258746130614601417 := by
  unfold tailWord_238880
  simp only [CollatzResearch.WordTrace]
  refine ⟨4356334687293016150529047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5808446249724021534038729 4356334687293016150529047)
  ·
    refine ⟨6534502030939524225793571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4356334687293016150529047 6534502030939524225793571)
    ·
      refine ⟨9801753046409286338690357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6534502030939524225793571 9801753046409286338690357)
      ·
        refine ⟨918914348100870594252221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9801753046409286338690357 918914348100870594252221)
        ·
          refine ⟨344592880537826472844583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 918914348100870594252221 344592880537826472844583)
          ·
            refine ⟨516889320806739709266875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344592880537826472844583 516889320806739709266875)
            ·
              refine ⟨775333981210109563900313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 516889320806739709266875 775333981210109563900313)
              ·
                refine ⟨581500485907582172925235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 775333981210109563900313 581500485907582172925235)
                ·
                  refine ⟨872250728861373259387853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 581500485907582172925235 872250728861373259387853)
                  ·
                    refine ⟨327094023323014972270445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 872250728861373259387853 327094023323014972270445)
                    ·
                      refine ⟨122660258746130614601417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 327094023323014972270445 122660258746130614601417)
                      ·
                        rfl

theorem cell23_238880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_238880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_238880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_238880 prefixEnd_238880 := by exact prefixLift 238880
  have htrace : WordTrace (prefixWord ++ tailWord_238880) baseStart_238880 baseEnd_238880 := by
    simpa [prefixWord, tailWord_238880, baseEnd_238880] using wordTrace_append hprefix tailTrace_238880
  have hstable : (prefixWord ++ tailWord_238880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238880).length < 2 ^ (prefixWord ++ tailWord_238880).sum := by decide
  have hdescent : baseEnd_238880 < baseStart_238880 := by decide
  rcases family_descends (prefixWord ++ tailWord_238880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238896 : List Nat := [2, 1, 1, 1, 2, 2, 4, 2, 2, 6]
def baseStart_238896 : Nat := 118140960795 + 238896 * 2 ^ 59
def prefixEnd_238896 : Nat := 4983230072969 + 3 ^ 40 * 238896 * 2
def baseEnd_238896 : Nat := 40889491478867517333781

theorem tailTrace_238896 : CollatzResearch.WordTrace tailWord_238896 prefixEnd_238896 40889491478867517333781 := by
  unfold tailWord_238896
  simp only [CollatzResearch.WordTrace]
  refine ⟨4356626471264033516820271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5808835295018711355760361 4356626471264033516820271)
  ·
    refine ⟨6534939706896050275230407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4356626471264033516820271 6534939706896050275230407)
    ·
      refine ⟨9802409560344075412845611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6534939706896050275230407 9802409560344075412845611)
      ·
        refine ⟨14703614340516113119268417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9802409560344075412845611 14703614340516113119268417)
        ·
          refine ⟨11027710755387084839451313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14703614340516113119268417 11027710755387084839451313)
          ·
            refine ⟨8270783066540313629588485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11027710755387084839451313 8270783066540313629588485)
            ·
              refine ⟨1550771824976308805547841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8270783066540313629588485 1550771824976308805547841)
              ·
                refine ⟨1163078868732231604160881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1550771824976308805547841 1163078868732231604160881)
                ·
                  refine ⟨872309151549173703120661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1163078868732231604160881 872309151549173703120661)
                  ·
                    refine ⟨40889491478867517333781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 872309151549173703120661 40889491478867517333781)
                    ·
                      rfl

theorem cell23_238896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 2, 6].length) (baseStart_238896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_238896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_238896 prefixEnd_238896 := by exact prefixLift 238896
  have htrace : WordTrace (prefixWord ++ tailWord_238896) baseStart_238896 baseEnd_238896 := by
    simpa [prefixWord, tailWord_238896, baseEnd_238896] using wordTrace_append hprefix tailTrace_238896
  have hstable : (prefixWord ++ tailWord_238896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238896).length < 2 ^ (prefixWord ++ tailWord_238896).sum := by decide
  have hdescent : baseEnd_238896 < baseStart_238896 := by decide
  rcases family_descends (prefixWord ++ tailWord_238896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238897 : List Nat := [1, 2, 2, 3, 3, 2, 2, 2, 2, 1, 3]
def baseStart_238897 : Nat := 118140960795 + 238897 * 2 ^ 59
def prefixEnd_238897 : Nat := 4983230072969 + 3 ^ 40 * 238897 * 2
def baseEnd_238897 : Nat := 122668987917257048088839

theorem tailTrace_238897 : CollatzResearch.WordTrace tailWord_238897 prefixEnd_238897 122668987917257048088839 := by
  unfold tailWord_238897
  simp only [CollatzResearch.WordTrace]
  refine ⟨8713289415524444204426945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5808859610349629469617963 8713289415524444204426945)
  ·
    refine ⟨6534967061643333153320209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8713289415524444204426945 6534967061643333153320209)
    ·
      refine ⟨4901225296232499864990157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6534967061643333153320209 4901225296232499864990157)
      ·
        refine ⟨1837959486087187449371309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4901225296232499864990157 1837959486087187449371309)
        ·
          refine ⟨689234807282695293514241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1837959486087187449371309 689234807282695293514241)
          ·
            refine ⟨516926105462021470135681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 689234807282695293514241 516926105462021470135681)
            ·
              refine ⟨387694579096516102601761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 516926105462021470135681 387694579096516102601761)
              ·
                refine ⟨290770934322387076951321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 387694579096516102601761 290770934322387076951321)
                ·
                  refine ⟨218078200741790307713491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 290770934322387076951321 218078200741790307713491)
                  ·
                    refine ⟨327117301112685461570237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 218078200741790307713491 327117301112685461570237)
                    ·
                      refine ⟨122668987917257048088839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 327117301112685461570237 122668987917257048088839)
                      ·
                        rfl

theorem cell23_238897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_238897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_238897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_238897 prefixEnd_238897 := by exact prefixLift 238897
  have htrace : WordTrace (prefixWord ++ tailWord_238897) baseStart_238897 baseEnd_238897 := by
    simpa [prefixWord, tailWord_238897, baseEnd_238897] using wordTrace_append hprefix tailTrace_238897
  have hstable : (prefixWord ++ tailWord_238897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238897).length < 2 ^ (prefixWord ++ tailWord_238897).sum := by decide
  have hdescent : baseEnd_238897 < baseStart_238897 := by decide
  rcases family_descends (prefixWord ++ tailWord_238897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238913 : List Nat := [1, 2, 5, 2, 1, 1, 1, 1, 1, 8]
def baseStart_238913 : Nat := 118140960795 + 238913 * 2 ^ 59
def prefixEnd_238913 : Nat := 4983230072969 + 3 ^ 40 * 238913 * 2
def baseEnd_238913 : Nat := 40892401202576328496255

theorem tailTrace_238913 : CollatzResearch.WordTrace tailWord_238913 prefixEnd_238913 40892401202576328496255 := by
  unfold tailWord_238913
  simp only [CollatzResearch.WordTrace]
  refine ⟨8713872983466478937009393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5809248655644319291339595 8713872983466478937009393)
  ·
    refine ⟨6535404737599859202757045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8713872983466478937009393 6535404737599859202757045)
    ·
      refine ⟨612694194149986800258473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6535404737599859202757045 612694194149986800258473)
      ·
        refine ⟨459520645612490100193855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 612694194149986800258473 459520645612490100193855)
        ·
          refine ⟨689280968418735150290783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459520645612490100193855 689280968418735150290783)
          ·
            refine ⟨1033921452628102725436175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 689280968418735150290783 1033921452628102725436175)
            ·
              refine ⟨1550882178942154088154263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1033921452628102725436175 1550882178942154088154263)
              ·
                refine ⟨2326323268413231132231395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1550882178942154088154263 2326323268413231132231395)
                ·
                  refine ⟨3489484902619846698347093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2326323268413231132231395 3489484902619846698347093)
                  ·
                    refine ⟨40892401202576328496255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3489484902619846698347093 40892401202576328496255)
                    ·
                      rfl

theorem cell23_238913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_238913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_238913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_238913 prefixEnd_238913 := by exact prefixLift 238913
  have htrace : WordTrace (prefixWord ++ tailWord_238913) baseStart_238913 baseEnd_238913 := by
    simpa [prefixWord, tailWord_238913, baseEnd_238913] using wordTrace_append hprefix tailTrace_238913
  have hstable : (prefixWord ++ tailWord_238913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238913).length < 2 ^ (prefixWord ++ tailWord_238913).sum := by decide
  have hdescent : baseEnd_238913 < baseStart_238913 := by decide
  rcases family_descends (prefixWord ++ tailWord_238913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238920 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 6, 2, 2]
def baseStart_238920 : Nat := 118140960795 + 238920 * 2 ^ 59
def prefixEnd_238920 : Nat := 4983230072969 + 3 ^ 40 * 238920 * 2
def baseEnd_238920 : Nat := 122680797972310458101233

theorem tailTrace_238920 : CollatzResearch.WordTrace tailWord_238920 prefixEnd_238920 122680797972310458101233 := by
  unfold tailWord_238920
  simp only [CollatzResearch.WordTrace]
  refine ⟨4357064147220559566257107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5809418862960746088342809 4357064147220559566257107)
  ·
    refine ⟨6535596220830839349385661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4357064147220559566257107 6535596220830839349385661)
    ·
      refine ⟨2450848582811564756019623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6535596220830839349385661 2450848582811564756019623)
      ·
        refine ⟨3676272874217347134029435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2450848582811564756019623 3676272874217347134029435)
        ·
          refine ⟨5514409311326020701044153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3676272874217347134029435 5514409311326020701044153)
          ·
            refine ⟨4135806983494515525783115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5514409311326020701044153 4135806983494515525783115)
            ·
              refine ⟨6203710475241773288674673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4135806983494515525783115 6203710475241773288674673)
              ·
                refine ⟨4652782856431329966506005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6203710475241773288674673 4652782856431329966506005)
                ·
                  refine ⟨218099196395218592179969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4652782856431329966506005 218099196395218592179969)
                  ·
                    refine ⟨163574397296413944134977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 218099196395218592179969 163574397296413944134977)
                    ·
                      refine ⟨122680797972310458101233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 163574397296413944134977 122680797972310458101233)
                      ·
                        rfl

theorem cell23_238920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 6, 2, 2].length) (baseStart_238920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_238920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_238920 prefixEnd_238920 := by exact prefixLift 238920
  have htrace : WordTrace (prefixWord ++ tailWord_238920) baseStart_238920 baseEnd_238920 := by
    simpa [prefixWord, tailWord_238920, baseEnd_238920] using wordTrace_append hprefix tailTrace_238920
  have hstable : (prefixWord ++ tailWord_238920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238920).length < 2 ^ (prefixWord ++ tailWord_238920).sum := by decide
  have hdescent : baseEnd_238920 < baseStart_238920 := by decide
  rcases family_descends (prefixWord ++ tailWord_238920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238954 : List Nat := [3, 1, 3, 3, 2, 1, 1, 1, 4, 2, 2]
def baseStart_238954 : Nat := 118140960795 + 238954 * 2 ^ 59
def prefixEnd_238954 : Nat := 4983230072969 + 3 ^ 40 * 238954 * 2
def baseEnd_238954 : Nat := 122698256314563325076077

theorem tailTrace_238954 : CollatzResearch.WordTrace tailWord_238954 prefixEnd_238954 122698256314563325076077 := by
  unfold tailWord_238954
  simp only [CollatzResearch.WordTrace]
  refine ⟨2178842094079485734812979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5810245584211961959501277 2178842094079485734812979)
  ·
    refine ⟨3268263141119228602219469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2178842094079485734812979 3268263141119228602219469)
    ·
      refine ⟨1225598677919710725832301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3268263141119228602219469 1225598677919710725832301)
      ·
        refine ⟨459599504219891522187113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1225598677919710725832301 459599504219891522187113)
        ·
          refine ⟨344699628164918641640335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 459599504219891522187113 344699628164918641640335)
          ·
            refine ⟨517049442247377962460503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344699628164918641640335 517049442247377962460503)
            ·
              refine ⟨775574163371066943690755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517049442247377962460503 775574163371066943690755)
              ·
                refine ⟨1163361245056600415536133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 775574163371066943690755 1163361245056600415536133)
                ·
                  refine ⟨218130233448112577913025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1163361245056600415536133 218130233448112577913025)
                  ·
                    refine ⟨163597675086084433434769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 218130233448112577913025 163597675086084433434769)
                    ·
                      refine ⟨122698256314563325076077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 163597675086084433434769 122698256314563325076077)
                      ·
                        rfl

theorem cell23_238954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_238954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_238954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_238954 prefixEnd_238954 := by exact prefixLift 238954
  have htrace : WordTrace (prefixWord ++ tailWord_238954) baseStart_238954 baseEnd_238954 := by
    simpa [prefixWord, tailWord_238954, baseEnd_238954] using wordTrace_append hprefix tailTrace_238954
  have hstable : (prefixWord ++ tailWord_238954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238954).length < 2 ^ (prefixWord ++ tailWord_238954).sum := by decide
  have hdescent : baseEnd_238954 < baseStart_238954 := by decide
  rcases family_descends (prefixWord ++ tailWord_238954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239010 : List Nat := [3, 3, 1, 2, 1, 2, 1, 1, 4, 1, 4]
def baseStart_239010 : Nat := 118140960795 + 239010 * 2 ^ 59
def prefixEnd_239010 : Nat := 4983230072969 + 3 ^ 40 * 239010 * 2
def baseEnd_239010 : Nat := 122727011231215105975819

theorem tailTrace_239010 : CollatzResearch.WordTrace tailWord_239010 prefixEnd_239010 122727011231215105975819 := by
  unfold tailWord_239010
  simp only [CollatzResearch.WordTrace]
  refine ⟨2179352716028766125822621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5811607242743376335526989 2179352716028766125822621)
  ·
    refine ⟨817257268510787297183483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2179352716028766125822621 817257268510787297183483)
    ·
      refine ⟨1225885902766180945775225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 817257268510787297183483 1225885902766180945775225)
      ·
        refine ⟨919414427074635709331419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1225885902766180945775225 919414427074635709331419)
        ·
          refine ⟨1379121640611953563997129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 919414427074635709331419 1379121640611953563997129)
          ·
            refine ⟨1034341230458965172997847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1379121640611953563997129 1034341230458965172997847)
            ·
              refine ⟨1551511845688447759496771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1034341230458965172997847 1551511845688447759496771)
              ·
                refine ⟨2327267768532671639245157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1551511845688447759496771 2327267768532671639245157)
                ·
                  refine ⟨436362706599875932358467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2327267768532671639245157 436362706599875932358467)
                  ·
                    refine ⟨654544059899813898537701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 436362706599875932358467 654544059899813898537701)
                    ·
                      refine ⟨122727011231215105975819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 654544059899813898537701 122727011231215105975819)
                      ·
                        rfl

theorem cell23_239010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_239010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239010 prefixEnd_239010 := by exact prefixLift 239010
  have htrace : WordTrace (prefixWord ++ tailWord_239010) baseStart_239010 baseEnd_239010 := by
    simpa [prefixWord, tailWord_239010, baseEnd_239010] using wordTrace_append hprefix tailTrace_239010
  have hstable : (prefixWord ++ tailWord_239010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239010).length < 2 ^ (prefixWord ++ tailWord_239010).sum := by decide
  have hdescent : baseEnd_239010 < baseStart_239010 := by decide
  rcases family_descends (prefixWord ++ tailWord_239010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239013 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 3, 4, 3]
def baseStart_239013 : Nat := 118140960795 + 239013 * 2 ^ 59
def prefixEnd_239013 : Nat := 4983230072969 + 3 ^ 40 * 239013 * 2
def baseEnd_239013 : Nat := 122728551673178594238305

theorem tailTrace_239013 : CollatzResearch.WordTrace tailWord_239013 prefixEnd_239013 122728551673178594238305 := by
  unfold tailWord_239013
  simp only [CollatzResearch.WordTrace]
  refine ⟨8717520283104196015649693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5811680188736130677099795 8717520283104196015649693)
  ·
    refine ⟨3269070106164073505868635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8717520283104196015649693 3269070106164073505868635)
    ·
      refine ⟨4903605159246110258802953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3269070106164073505868635 4903605159246110258802953)
      ·
        refine ⟨3677703869434582694102215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4903605159246110258802953 3677703869434582694102215)
        ·
          refine ⟨5516555804151874041153323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3677703869434582694102215 5516555804151874041153323)
          ·
            refine ⟨8274833706227811061729985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5516555804151874041153323 8274833706227811061729985)
            ·
              refine ⟨6206125279670858296297489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8274833706227811061729985 6206125279670858296297489)
              ·
                refine ⟨4654593959753143722223117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6206125279670858296297489 4654593959753143722223117)
                ·
                  refine ⟨1745472734907428895833669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4654593959753143722223117 1745472734907428895833669)
                  ·
                    refine ⟨327276137795142917968813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1745472734907428895833669 327276137795142917968813)
                    ·
                      refine ⟨122728551673178594238305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 327276137795142917968813 122728551673178594238305)
                      ·
                        rfl

theorem cell23_239013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 4, 3].length) (baseStart_239013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239013 prefixEnd_239013 := by exact prefixLift 239013
  have htrace : WordTrace (prefixWord ++ tailWord_239013) baseStart_239013 baseEnd_239013 := by
    simpa [prefixWord, tailWord_239013, baseEnd_239013] using wordTrace_append hprefix tailTrace_239013
  have hstable : (prefixWord ++ tailWord_239013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239013).length < 2 ^ (prefixWord ++ tailWord_239013).sum := by decide
  have hdescent : baseEnd_239013 < baseStart_239013 := by decide
  rcases family_descends (prefixWord ++ tailWord_239013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239020 : List Nat := [2, 2, 1, 1, 1, 1, 7, 1, 3, 4]
def baseStart_239020 : Nat := 118140960795 + 239020 * 2 ^ 59
def prefixEnd_239020 : Nat := 4983230072969 + 3 ^ 40 * 239020 * 2
def baseEnd_239020 : Nat := 40910715345920022283591

theorem tailTrace_239020 : CollatzResearch.WordTrace tailWord_239020 prefixEnd_239020 40910715345920022283591 := by
  unfold tailWord_239020
  simp only [CollatzResearch.WordTrace]
  refine ⟨4358887797039418105577257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5811850396052557474103009 4358887797039418105577257)
  ·
    refine ⟨3269165847779563579182943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4358887797039418105577257 3269165847779563579182943)
    ·
      refine ⟨4903748771669345368774415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3269165847779563579182943 4903748771669345368774415)
      ·
        refine ⟨7355623157504018053161623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4903748771669345368774415 7355623157504018053161623)
        ·
          refine ⟨11033434736256027079742435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7355623157504018053161623 11033434736256027079742435)
          ·
            refine ⟨16550152104384040619613653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11033434736256027079742435 16550152104384040619613653)
            ·
              refine ⟨387894189946500952022195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 16550152104384040619613653 387894189946500952022195)
              ·
                refine ⟨581841284919751428033293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 387894189946500952022195 581841284919751428033293)
                ·
                  refine ⟨218190481844906785512485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 581841284919751428033293 218190481844906785512485)
                  ·
                    refine ⟨40910715345920022283591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 218190481844906785512485 40910715345920022283591)
                    ·
                      rfl

theorem cell23_239020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 4].length) (baseStart_239020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239020 prefixEnd_239020 := by exact prefixLift 239020
  have htrace : WordTrace (prefixWord ++ tailWord_239020) baseStart_239020 baseEnd_239020 := by
    simpa [prefixWord, tailWord_239020, baseEnd_239020] using wordTrace_append hprefix tailTrace_239020
  have hstable : (prefixWord ++ tailWord_239020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239020).length < 2 ^ (prefixWord ++ tailWord_239020).sum := by decide
  have hdescent : baseEnd_239020 < baseStart_239020 := by decide
  rcases family_descends (prefixWord ++ tailWord_239020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239043 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 2, 5, 3]
def baseStart_239043 : Nat := 118140960795 + 239043 * 2 ^ 59
def prefixEnd_239043 : Nat := 4983230072969 + 3 ^ 40 * 239043 * 2
def baseEnd_239043 : Nat := 122743956092813476863167

theorem tailTrace_239043 : CollatzResearch.WordTrace tailWord_239043 prefixEnd_239043 122743956092813476863167 := by
  unfold tailWord_239043
  simp only [CollatzResearch.WordTrace]
  refine ⟨8718614472995511139241783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5812409648663674092827855 8718614472995511139241783)
  ·
    refine ⟨13077921709493266708862675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8718614472995511139241783 13077921709493266708862675)
    ·
      refine ⟨19616882564239900063294013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13077921709493266708862675 19616882564239900063294013)
      ·
        refine ⟨7356330961589962523735255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19616882564239900063294013 7356330961589962523735255)
        ·
          refine ⟨11034496442384943785602883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7356330961589962523735255 11034496442384943785602883)
          ·
            refine ⟨16551744663577415678404325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11034496442384943785602883 16551744663577415678404325)
            ·
              refine ⟨3103452124420765439700811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16551744663577415678404325 3103452124420765439700811)
              ·
                refine ⟨4655178186631148159551217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3103452124420765439700811 4655178186631148159551217)
                ·
                  refine ⟨3491383639973361119663413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4655178186631148159551217 3491383639973361119663413)
                  ·
                    refine ⟨327317216247502604968445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3491383639973361119663413 327317216247502604968445)
                    ·
                      refine ⟨122743956092813476863167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 327317216247502604968445 122743956092813476863167)
                      ·
                        rfl

theorem cell23_239043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 5, 3].length) (baseStart_239043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239043 prefixEnd_239043 := by exact prefixLift 239043
  have htrace : WordTrace (prefixWord ++ tailWord_239043) baseStart_239043 baseEnd_239043 := by
    simpa [prefixWord, tailWord_239043, baseEnd_239043] using wordTrace_append hprefix tailTrace_239043
  have hstable : (prefixWord ++ tailWord_239043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239043).length < 2 ^ (prefixWord ++ tailWord_239043).sum := by decide
  have hdescent : baseEnd_239043 < baseStart_239043 := by decide
  rcases family_descends (prefixWord ++ tailWord_239043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239094 : List Nat := [5, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3]
def baseStart_239094 : Nat := 118140960795 + 239094 * 2 ^ 59
def prefixEnd_239094 : Nat := 4983230072969 + 3 ^ 40 * 239094 * 2
def baseEnd_239094 : Nat := 122770143606192777325433

theorem tailTrace_239094 : CollatzResearch.WordTrace tailWord_239094 prefixEnd_239094 122770143606192777325433 := by
  unfold tailWord_239094
  simp only [CollatzResearch.WordTrace]
  refine ⟨545029662238171678084271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5813649730540497899565557 545029662238171678084271)
  ·
    refine ⟨817544493357257517126407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 545029662238171678084271 817544493357257517126407)
    ·
      refine ⟨1226316740035886275689611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 817544493357257517126407 1226316740035886275689611)
      ·
        refine ⟨1839475110053829413534417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1226316740035886275689611 1839475110053829413534417)
        ·
          refine ⟨1379606332540372060150813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1839475110053829413534417 1379606332540372060150813)
          ·
            refine ⟨517352374702639522556555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1379606332540372060150813 517352374702639522556555)
            ·
              refine ⟨776028562053959283834833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517352374702639522556555 776028562053959283834833)
              ·
                refine ⟨582021421540469462876125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 776028562053959283834833 582021421540469462876125)
                ·
                  refine ⟨218258033077676048578547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 582021421540469462876125 218258033077676048578547)
                  ·
                    refine ⟨327387049616514072867821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 218258033077676048578547 327387049616514072867821)
                    ·
                      refine ⟨122770143606192777325433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 327387049616514072867821 122770143606192777325433)
                      ·
                        rfl

theorem cell23_239094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_239094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239094 prefixEnd_239094 := by exact prefixLift 239094
  have htrace : WordTrace (prefixWord ++ tailWord_239094) baseStart_239094 baseEnd_239094 := by
    simpa [prefixWord, tailWord_239094, baseEnd_239094] using wordTrace_append hprefix tailTrace_239094
  have hstable : (prefixWord ++ tailWord_239094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239094).length < 2 ^ (prefixWord ++ tailWord_239094).sum := by decide
  have hdescent : baseEnd_239094 < baseStart_239094 := by decide
  rcases family_descends (prefixWord ++ tailWord_239094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239100 : List Nat := [2, 2, 2, 1, 2, 1, 4, 1, 3, 1, 4]
def baseStart_239100 : Nat := 118140960795 + 239100 * 2 ^ 59
def prefixEnd_239100 : Nat := 4983230072969 + 3 ^ 40 * 239100 * 2
def baseEnd_239100 : Nat := 122773224490119753850405

theorem tailTrace_239100 : CollatzResearch.WordTrace tailWord_239100 prefixEnd_239100 122773224490119753850405 := by
  unfold tailWord_239100
  simp only [CollatzResearch.WordTrace]
  refine ⟨4360346716894504937033377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5813795622526006582711169 4360346716894504937033377)
  ·
    refine ⟨3270260037670878702775033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4360346716894504937033377 3270260037670878702775033)
    ·
      refine ⟨2452695028253159027081275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3270260037670878702775033 2452695028253159027081275)
      ·
        refine ⟨3679042542379738540621913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2452695028253159027081275 3679042542379738540621913)
        ·
          refine ⟨2759281906784803905466435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3679042542379738540621913 2759281906784803905466435)
          ·
            refine ⟨4138922860177205858199653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2759281906784803905466435 4138922860177205858199653)
            ·
              refine ⟨776048036283226098412435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4138922860177205858199653 776048036283226098412435)
              ·
                refine ⟨1164072054424839147618653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 776048036283226098412435 1164072054424839147618653)
                ·
                  refine ⟨436527020409314680356995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1164072054424839147618653 436527020409314680356995)
                  ·
                    refine ⟨654790530613972020535493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 436527020409314680356995 654790530613972020535493)
                    ·
                      refine ⟨122773224490119753850405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 654790530613972020535493 122773224490119753850405)
                      ·
                        rfl

theorem cell23_239100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_239100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239100 prefixEnd_239100 := by exact prefixLift 239100
  have htrace : WordTrace (prefixWord ++ tailWord_239100) baseStart_239100 baseEnd_239100 := by
    simpa [prefixWord, tailWord_239100, baseEnd_239100] using wordTrace_append hprefix tailTrace_239100
  have hstable : (prefixWord ++ tailWord_239100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239100).length < 2 ^ (prefixWord ++ tailWord_239100).sum := by decide
  have hdescent : baseEnd_239100 < baseStart_239100 := by decide
  rcases family_descends (prefixWord ++ tailWord_239100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239103 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 5]
def baseStart_239103 : Nat := 118140960795 + 239103 * 2 ^ 59
def prefixEnd_239103 : Nat := 4983230072969 + 3 ^ 40 * 239103 * 2
def baseEnd_239103 : Nat := 122774764932083242112891

theorem tailTrace_239103 : CollatzResearch.WordTrace tailWord_239103 prefixEnd_239103 122774764932083242112891 := by
  unfold tailWord_239103
  simp only [CollatzResearch.WordTrace]
  refine ⟨8720802852778141386425963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5813868568518760924283975 8720802852778141386425963)
  ·
    refine ⟨13081204279167212079638945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8720802852778141386425963 13081204279167212079638945)
    ·
      refine ⟨9810903209375409059729209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13081204279167212079638945 9810903209375409059729209)
      ·
        refine ⟨7358177407031556794796907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9810903209375409059729209 7358177407031556794796907)
        ·
          refine ⟨11037266110547335192195361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7358177407031556794796907 11037266110547335192195361)
          ·
            refine ⟨8277949582910501394146521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11037266110547335192195361 8277949582910501394146521)
            ·
              refine ⟨6208462187182876045609891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8277949582910501394146521 6208462187182876045609891)
              ·
                refine ⟨9312693280774314068414837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6208462187182876045609891 9312693280774314068414837)
                ·
                  refine ⟨873064995072591943913891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9312693280774314068414837 873064995072591943913891)
                  ·
                    refine ⟨1309597492608887915870837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 873064995072591943913891 1309597492608887915870837)
                    ·
                      refine ⟨122774764932083242112891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1309597492608887915870837 122774764932083242112891)
                      ·
                        rfl

theorem cell23_239103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 5].length) (baseStart_239103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239103 prefixEnd_239103 := by exact prefixLift 239103
  have htrace : WordTrace (prefixWord ++ tailWord_239103) baseStart_239103 baseEnd_239103 := by
    simpa [prefixWord, tailWord_239103, baseEnd_239103] using wordTrace_append hprefix tailTrace_239103
  have hstable : (prefixWord ++ tailWord_239103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239103).length < 2 ^ (prefixWord ++ tailWord_239103).sum := by decide
  have hdescent : baseEnd_239103 < baseStart_239103 := by decide
  rcases family_descends (prefixWord ++ tailWord_239103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239111 : List Nat := [1, 1, 4, 3, 2, 2, 2, 3, 1, 1, 3]
def baseStart_239111 : Nat := 118140960795 + 239111 * 2 ^ 59
def prefixEnd_239111 : Nat := 4983230072969 + 3 ^ 40 * 239111 * 2
def baseEnd_239111 : Nat := 122778872777319210812855

theorem tailTrace_239111 : CollatzResearch.WordTrace tailWord_239111 prefixEnd_239111 122778872777319210812855 := by
  unfold tailWord_239111
  simp only [CollatzResearch.WordTrace]
  refine ⟨8721094636749158752717187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5814063091166105835144791 8721094636749158752717187)
  ·
    refine ⟨13081641955123738129075781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8721094636749158752717187 13081641955123738129075781)
    ·
      refine ⟨2452807866585700899201709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13081641955123738129075781 2452807866585700899201709)
      ·
        refine ⟨919802949969637837200641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2452807866585700899201709 919802949969637837200641)
        ·
          refine ⟨689852212477228377900481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 919802949969637837200641 689852212477228377900481)
          ·
            refine ⟨517389159357921283425361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 689852212477228377900481 517389159357921283425361)
            ·
              refine ⟨388041869518440962569021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 517389159357921283425361 388041869518440962569021)
              ·
                refine ⟨145515701069415360963383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 388041869518440962569021 145515701069415360963383)
                ·
                  refine ⟨218273551604123041445075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145515701069415360963383 218273551604123041445075)
                  ·
                    refine ⟨327410327406184562167613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 218273551604123041445075 327410327406184562167613)
                    ·
                      refine ⟨122778872777319210812855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 327410327406184562167613 122778872777319210812855)
                      ·
                        rfl

theorem cell23_239111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_239111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239111 prefixEnd_239111 := by exact prefixLift 239111
  have htrace : WordTrace (prefixWord ++ tailWord_239111) baseStart_239111 baseEnd_239111 := by
    simpa [prefixWord, tailWord_239111, baseEnd_239111] using wordTrace_append hprefix tailTrace_239111
  have hstable : (prefixWord ++ tailWord_239111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239111).length < 2 ^ (prefixWord ++ tailWord_239111).sum := by decide
  have hdescent : baseEnd_239111 < baseStart_239111 := by decide
  rcases family_descends (prefixWord ++ tailWord_239111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239114 : List Nat := [3, 1, 2, 2, 2, 4, 2, 1, 1, 5]
def baseStart_239114 : Nat := 118140960795 + 239114 * 2 ^ 59
def prefixEnd_239114 : Nat := 4983230072969 + 3 ^ 40 * 239114 * 2
def baseEnd_239114 : Nat := 40926804406427566358447

theorem tailTrace_239114 : CollatzResearch.WordTrace tailWord_239114 prefixEnd_239114 40926804406427566358447 := by
  unfold tailWord_239114
  simp only [CollatzResearch.WordTrace]
  refine ⟨2180301013934572566269099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5814136037158860176717597 2180301013934572566269099)
  ·
    refine ⟨3270451520901858849403649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2180301013934572566269099 3270451520901858849403649)
    ·
      refine ⟨2452838640676394137052737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3270451520901858849403649 2452838640676394137052737)
      ·
        refine ⟨1839628980507295602789553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2452838640676394137052737 1839628980507295602789553)
        ·
          refine ⟨1379721735380471702092165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1839628980507295602789553 1379721735380471702092165)
          ·
            refine ⟨258697825383838444142281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1379721735380471702092165 258697825383838444142281)
            ·
              refine ⟨194023369037878833106711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258697825383838444142281 194023369037878833106711)
              ·
                refine ⟨291035053556818249660067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194023369037878833106711 291035053556818249660067)
                ·
                  refine ⟨436552580335227374490101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 291035053556818249660067 436552580335227374490101)
                  ·
                    refine ⟨40926804406427566358447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 436552580335227374490101 40926804406427566358447)
                    ·
                      rfl

theorem cell23_239114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 1, 1, 5].length) (baseStart_239114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239114 prefixEnd_239114 := by exact prefixLift 239114
  have htrace : WordTrace (prefixWord ++ tailWord_239114) baseStart_239114 baseEnd_239114 := by
    simpa [prefixWord, tailWord_239114, baseEnd_239114] using wordTrace_append hprefix tailTrace_239114
  have hstable : (prefixWord ++ tailWord_239114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239114).length < 2 ^ (prefixWord ++ tailWord_239114).sum := by decide
  have hdescent : baseEnd_239114 < baseStart_239114 := by decide
  rcases family_descends (prefixWord ++ tailWord_239114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239123 : List Nat := [1, 1, 1, 2, 1, 7, 10]
def baseStart_239123 : Nat := 118140960795 + 239123 * 2 ^ 59
def prefixEnd_239123 : Nat := 4983230072969 + 3 ^ 40 * 239123 * 2
def baseEnd_239123 : Nat := 1515864624014483504479

theorem tailTrace_239123 : CollatzResearch.WordTrace tailWord_239123 prefixEnd_239123 1515864624014483504479 := by
  unfold tailWord_239123
  simp only [CollatzResearch.WordTrace]
  refine ⟨8721532312705684802154023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5814354875137123201436015 8721532312705684802154023)
  ·
    refine ⟨13082298469058527203231035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8721532312705684802154023 13082298469058527203231035)
    ·
      refine ⟨19623447703587790804846553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13082298469058527203231035 19623447703587790804846553)
      ·
        refine ⟨14717585777690843103634915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19623447703587790804846553 14717585777690843103634915)
        ·
          refine ⟨22076378666536264655452373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14717585777690843103634915 22076378666536264655452373)
          ·
            refine ⟨517415124996943702862165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 22076378666536264655452373 517415124996943702862165)
            ·
              refine ⟨1515864624014483504479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 517415124996943702862165 1515864624014483504479)
              ·
                rfl

theorem cell23_239123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 10].length) (baseStart_239123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239123 prefixEnd_239123 := by exact prefixLift 239123
  have htrace : WordTrace (prefixWord ++ tailWord_239123) baseStart_239123 baseEnd_239123 := by
    simpa [prefixWord, tailWord_239123, baseEnd_239123] using wordTrace_append hprefix tailTrace_239123
  have hstable : (prefixWord ++ tailWord_239123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239123).length < 2 ^ (prefixWord ++ tailWord_239123).sum := by decide
  have hdescent : baseEnd_239123 < baseStart_239123 := by decide
  rcases family_descends (prefixWord ++ tailWord_239123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239144 : List Nat := [2, 1, 5, 2, 2, 2, 1, 1, 1, 6]
def baseStart_239144 : Nat := 118140960795 + 239144 * 2 ^ 59
def prefixEnd_239144 : Nat := 4983230072969 + 3 ^ 40 * 239144 * 2
def baseEnd_239144 : Nat := 40931939212972527233401

theorem tailTrace_239144 : CollatzResearch.WordTrace tailWord_239144 prefixEnd_239144 40931939212972527233401 := by
  unfold tailWord_239144
  simp only [CollatzResearch.WordTrace]
  refine ⟨4361149122814802694334243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5814865497086403592445657 4361149122814802694334243)
  ·
    refine ⟨6541723684222204041501365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4361149122814802694334243 6541723684222204041501365)
    ·
      refine ⟨613286595395831628890753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6541723684222204041501365 613286595395831628890753)
      ·
        refine ⟨459964946546873721668065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 613286595395831628890753 459964946546873721668065)
        ·
          refine ⟨344973709910155291251049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 459964946546873721668065 344973709910155291251049)
          ·
            refine ⟨258730282432616468438287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344973709910155291251049 258730282432616468438287)
            ·
              refine ⟨388095423648924702657431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258730282432616468438287 388095423648924702657431)
              ·
                refine ⟨582143135473387053986147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 388095423648924702657431 582143135473387053986147)
                ·
                  refine ⟨873214703210080580979221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 582143135473387053986147 873214703210080580979221)
                  ·
                    refine ⟨40931939212972527233401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 873214703210080580979221 40931939212972527233401)
                    ·
                      rfl

theorem cell23_239144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_239144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239144 prefixEnd_239144 := by exact prefixLift 239144
  have htrace : WordTrace (prefixWord ++ tailWord_239144) baseStart_239144 baseEnd_239144 := by
    simpa [prefixWord, tailWord_239144, baseEnd_239144] using wordTrace_append hprefix tailTrace_239144
  have hstable : (prefixWord ++ tailWord_239144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239144).length < 2 ^ (prefixWord ++ tailWord_239144).sum := by decide
  have hdescent : baseEnd_239144 < baseStart_239144 := by decide
  rcases family_descends (prefixWord ++ tailWord_239144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239157 : List Nat := [1, 3, 3, 1, 1, 5, 2, 7]
def baseStart_239157 : Nat := 118140960795 + 239157 * 2 ^ 59
def prefixEnd_239157 : Nat := 4983230072969 + 3 ^ 40 * 239157 * 2
def baseEnd_239157 : Nat := 4548240477312075216209

theorem tailTrace_239157 : CollatzResearch.WordTrace tailWord_239157 prefixEnd_239157 4548240477312075216209 := by
  unfold tailWord_239157
  simp only [CollatzResearch.WordTrace]
  refine ⟨8722772394582508608891725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5815181596388339072594483 8722772394582508608891725)
  ·
    refine ⟨3271039647968440728334397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8722772394582508608891725 3271039647968440728334397)
    ·
      refine ⟨1226639867988165273125399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3271039647968440728334397 1226639867988165273125399)
      ·
        refine ⟨1839959801982247909688099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1226639867988165273125399 1839959801982247909688099)
        ·
          refine ⟨2759939702973371864532149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1839959801982247909688099 2759939702973371864532149)
          ·
            refine ⟨258744347153753612299889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2759939702973371864532149 258744347153753612299889)
            ·
              refine ⟨194058260365315209224917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258744347153753612299889 194058260365315209224917)
              ·
                refine ⟨4548240477312075216209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 194058260365315209224917 4548240477312075216209)
                ·
                  rfl

theorem cell23_239157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 7].length) (baseStart_239157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239157 prefixEnd_239157 := by exact prefixLift 239157
  have htrace : WordTrace (prefixWord ++ tailWord_239157) baseStart_239157 baseEnd_239157 := by
    simpa [prefixWord, tailWord_239157, baseEnd_239157] using wordTrace_append hprefix tailTrace_239157
  have hstable : (prefixWord ++ tailWord_239157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239157).length < 2 ^ (prefixWord ++ tailWord_239157).sum := by decide
  have hdescent : baseEnd_239157 < baseStart_239157 := by decide
  rcases family_descends (prefixWord ++ tailWord_239157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239167 : List Nat := [1, 1, 2, 2, 3, 3, 1, 2, 4, 1, 3]
def baseStart_239167 : Nat := 118140960795 + 239167 * 2 ^ 59
def prefixEnd_239167 : Nat := 4983230072969 + 3 ^ 40 * 239167 * 2
def baseEnd_239167 : Nat := 122807627693970991712597

theorem tailTrace_239167 : CollatzResearch.WordTrace tailWord_239167 prefixEnd_239167 122807627693970991712597 := by
  unfold tailWord_239167
  simp only [CollatzResearch.WordTrace]
  refine ⟨8723137124546280316755755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5815424749697520211170503 8723137124546280316755755)
  ·
    refine ⟨13084705686819420475133633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8723137124546280316755755 13084705686819420475133633)
    ·
      refine ⟨9813529265114565356350225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13084705686819420475133633 9813529265114565356350225)
      ·
        refine ⟨7360146948835924017262669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9813529265114565356350225 7360146948835924017262669)
        ·
          refine ⟨2760055105813471506473501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7360146948835924017262669 2760055105813471506473501)
          ·
            refine ⟨1035020664680051814927563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2760055105813471506473501 1035020664680051814927563)
            ·
              refine ⟨1552530997020077722391345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1035020664680051814927563 1552530997020077722391345)
              ·
                refine ⟨1164398247765058291793509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1552530997020077722391345 1164398247765058291793509)
                ·
                  refine ⟨218324671455948429711283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1164398247765058291793509 218324671455948429711283)
                  ·
                    refine ⟨327487007183922644566925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 218324671455948429711283 327487007183922644566925)
                    ·
                      refine ⟨122807627693970991712597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 327487007183922644566925 122807627693970991712597)
                      ·
                        rfl

theorem cell23_239167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 4, 1, 3].length) (baseStart_239167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239167 prefixEnd_239167 := by exact prefixLift 239167
  have htrace : WordTrace (prefixWord ++ tailWord_239167) baseStart_239167 baseEnd_239167 := by
    simpa [prefixWord, tailWord_239167, baseEnd_239167] using wordTrace_append hprefix tailTrace_239167
  have hstable : (prefixWord ++ tailWord_239167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239167).length < 2 ^ (prefixWord ++ tailWord_239167).sum := by decide
  have hdescent : baseEnd_239167 < baseStart_239167 := by decide
  rcases family_descends (prefixWord ++ tailWord_239167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239174 : List Nat := [6, 1, 1, 1, 3, 2, 9]
def baseStart_239174 : Nat := 118140960795 + 239174 * 2 ^ 59
def prefixEnd_239174 : Nat := 4983230072969 + 3 ^ 40 * 239174 * 2
def baseEnd_239174 : Nat := 1516187926648795855865

theorem tailTrace_239174 : CollatzResearch.WordTrace tailWord_239174 prefixEnd_239174 1516187926648795855865 := by
  unfold tailWord_239174
  simp only [CollatzResearch.WordTrace]
  refine ⟨272606013610028766008143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5815594957013947008173717 272606013610028766008143)
  ·
    refine ⟨408909020415043149012215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272606013610028766008143 408909020415043149012215)
    ·
      refine ⟨613363530622564723518323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408909020415043149012215 613363530622564723518323)
      ·
        refine ⟨920045295933847085277485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613363530622564723518323 920045295933847085277485)
        ·
          refine ⟨345016985975192656979057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 920045295933847085277485 345016985975192656979057)
          ·
            refine ⟨258762739481394492734293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345016985975192656979057 258762739481394492734293)
            ·
              refine ⟨1516187926648795855865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 258762739481394492734293 1516187926648795855865)
              ·
                rfl

theorem cell23_239174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 9].length) (baseStart_239174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239174 prefixEnd_239174 := by exact prefixLift 239174
  have htrace : WordTrace (prefixWord ++ tailWord_239174) baseStart_239174 baseEnd_239174 := by
    simpa [prefixWord, tailWord_239174, baseEnd_239174] using wordTrace_append hprefix tailTrace_239174
  have hstable : (prefixWord ++ tailWord_239174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239174).length < 2 ^ (prefixWord ++ tailWord_239174).sum := by decide
  have hdescent : baseEnd_239174 < baseStart_239174 := by decide
  rcases family_descends (prefixWord ++ tailWord_239174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239267 : List Nat := [1, 1, 1, 4, 1, 1, 3, 2, 2, 5, 2]
def baseStart_239267 : Nat := 118140960795 + 239267 * 2 ^ 59
def prefixEnd_239267 : Nat := 4983230072969 + 3 ^ 40 * 239267 * 2
def baseEnd_239267 : Nat := 122858975759420600462137

theorem tailTrace_239267 : CollatzResearch.WordTrace tailWord_239267 prefixEnd_239267 122858975759420600462137 := by
  unfold tailWord_239267
  simp only [CollatzResearch.WordTrace]
  refine ⟨8726784424183997395396055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5817856282789331596930703 8726784424183997395396055)
  ·
    refine ⟨13090176636275996093094083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8726784424183997395396055 13090176636275996093094083)
    ·
      refine ⟨19635264954413994139641125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13090176636275996093094083 19635264954413994139641125)
      ·
        refine ⟨3681612178952623901182711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19635264954413994139641125 3681612178952623901182711)
        ·
          refine ⟨5522418268428935851774067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3681612178952623901182711 5522418268428935851774067)
          ·
            refine ⟨8283627402643403777661101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5522418268428935851774067 8283627402643403777661101)
            ·
              refine ⟨3106360275991276416622913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8283627402643403777661101 3106360275991276416622913)
              ·
                refine ⟨2329770206993457312467185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3106360275991276416622913 2329770206993457312467185)
                ·
                  refine ⟨1747327655245092984350389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2329770206993457312467185 1747327655245092984350389)
                  ·
                    refine ⟨163811967679227467282849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1747327655245092984350389 163811967679227467282849)
                    ·
                      refine ⟨122858975759420600462137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 163811967679227467282849 122858975759420600462137)
                      ·
                        rfl

theorem cell23_239267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 5, 2].length) (baseStart_239267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239267 prefixEnd_239267 := by exact prefixLift 239267
  have htrace : WordTrace (prefixWord ++ tailWord_239267) baseStart_239267 baseEnd_239267 := by
    simpa [prefixWord, tailWord_239267, baseEnd_239267] using wordTrace_append hprefix tailTrace_239267
  have hstable : (prefixWord ++ tailWord_239267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239267).length < 2 ^ (prefixWord ++ tailWord_239267).sum := by decide
  have hdescent : baseEnd_239267 < baseStart_239267 := by decide
  rcases family_descends (prefixWord ++ tailWord_239267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239277 : List Nat := [1, 5, 2, 1, 1, 1, 3, 1, 1, 7]
def baseStart_239277 : Nat := 118140960795 + 239277 * 2 ^ 59
def prefixEnd_239277 : Nat := 4983230072969 + 3 ^ 40 * 239277 * 2
def baseEnd_239277 : Nat := 40954703521988520445697

theorem tailTrace_239277 : CollatzResearch.WordTrace tailWord_239277 prefixEnd_239277 40954703521988520445697 := by
  unfold tailWord_239277
  simp only [CollatzResearch.WordTrace]
  refine ⟨8727149154147769103260085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5818099436098512735506723 8727149154147769103260085)
  ·
    refine ⟨818170233201353353430633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8727149154147769103260085 818170233201353353430633)
    ·
      refine ⟨613627674901015015072975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 818170233201353353430633 613627674901015015072975)
      ·
        refine ⟨920441512351522522609463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613627674901015015072975 920441512351522522609463)
        ·
          refine ⟨1380662268527283783914195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 920441512351522522609463 1380662268527283783914195)
          ·
            refine ⟨2070993402790925675871293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1380662268527283783914195 2070993402790925675871293)
            ·
              refine ⟨776622526046597128451735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2070993402790925675871293 776622526046597128451735)
              ·
                refine ⟨1164933789069895692677603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 776622526046597128451735 1164933789069895692677603)
                ·
                  refine ⟨1747400683604843539016405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1164933789069895692677603 1747400683604843539016405)
                  ·
                    refine ⟨40954703521988520445697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1747400683604843539016405 40954703521988520445697)
                    ·
                      rfl

theorem cell23_239277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_239277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239277 prefixEnd_239277 := by exact prefixLift 239277
  have htrace : WordTrace (prefixWord ++ tailWord_239277) baseStart_239277 baseEnd_239277 := by
    simpa [prefixWord, tailWord_239277, baseEnd_239277] using wordTrace_append hprefix tailTrace_239277
  have hstable : (prefixWord ++ tailWord_239277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239277).length < 2 ^ (prefixWord ++ tailWord_239277).sum := by decide
  have hdescent : baseEnd_239277 < baseStart_239277 := by decide
  rcases family_descends (prefixWord ++ tailWord_239277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239298 : List Nat := [3, 5, 1, 2, 1, 1, 2, 1, 7]
def baseStart_239298 : Nat := 118140960795 + 239298 * 2 ^ 59
def prefixEnd_239298 : Nat := 4983230072969 + 3 ^ 40 * 239298 * 2
def baseEnd_239298 : Nat := 13652765962189997686055

theorem tailTrace_239298 : CollatzResearch.WordTrace tailWord_239298 prefixEnd_239298 13652765962189997686055 := by
  unfold tailWord_239298
  simp only [CollatzResearch.WordTrace]
  refine ⟨2181978771767922422443637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5818610058047793126516365 2181978771767922422443637)
  ·
    refine ⟨204560509853242727104091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2181978771767922422443637 204560509853242727104091)
    ·
      refine ⟨306840764779864090656137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204560509853242727104091 306840764779864090656137)
      ·
        refine ⟨230130573584898067992103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306840764779864090656137 230130573584898067992103)
        ·
          refine ⟨345195860377347101988155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230130573584898067992103 345195860377347101988155)
          ·
            refine ⟨517793790566020652982233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345195860377347101988155 517793790566020652982233)
            ·
              refine ⟨388345342924515489736675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 517793790566020652982233 388345342924515489736675)
              ·
                refine ⟨582518014386773234605013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 388345342924515489736675 582518014386773234605013)
                ·
                  refine ⟨13652765962189997686055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 582518014386773234605013 13652765962189997686055)
                  ·
                    rfl

theorem cell23_239298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_239298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239298 prefixEnd_239298 := by exact prefixLift 239298
  have htrace : WordTrace (prefixWord ++ tailWord_239298) baseStart_239298 baseEnd_239298 := by
    simpa [prefixWord, tailWord_239298, baseEnd_239298] using wordTrace_append hprefix tailTrace_239298
  have hstable : (prefixWord ++ tailWord_239298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239298).length < 2 ^ (prefixWord ++ tailWord_239298).sum := by decide
  have hdescent : baseEnd_239298 < baseStart_239298 := by decide
  rcases family_descends (prefixWord ++ tailWord_239298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239348 : List Nat := [2, 6, 1, 1, 1, 2, 1, 2, 2, 1, 4]
def baseStart_239348 : Nat := 118140960795 + 239348 * 2 ^ 59
def prefixEnd_239348 : Nat := 4983230072969 + 3 ^ 40 * 239348 * 2
def baseEnd_239348 : Nat := 122900567692434783549265

theorem tailTrace_239348 : CollatzResearch.WordTrace tailWord_239348 prefixEnd_239348 122900567692434783549265 := by
  unfold tailWord_239348
  simp only [CollatzResearch.WordTrace]
  refine ⟨4364869368445274114547349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5819825824593698819396465 4364869368445274114547349)
  ·
    refine ⟨204603251645872224119407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4364869368445274114547349 204603251645872224119407)
    ·
      refine ⟨306904877468808336179111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204603251645872224119407 306904877468808336179111)
      ·
        refine ⟨460357316203212504268667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306904877468808336179111 460357316203212504268667)
        ·
          refine ⟨690535974304818756403001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460357316203212504268667 690535974304818756403001)
          ·
            refine ⟨517901980728614067302251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 690535974304818756403001 517901980728614067302251)
            ·
              refine ⟨776852971092921100953377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517901980728614067302251 776852971092921100953377)
              ·
                refine ⟨582639728319690825715033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 776852971092921100953377 582639728319690825715033)
                ·
                  refine ⟨436979796239768119286275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 582639728319690825715033 436979796239768119286275)
                  ·
                    refine ⟨655469694359652178929413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 436979796239768119286275 655469694359652178929413)
                    ·
                      refine ⟨122900567692434783549265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 655469694359652178929413 122900567692434783549265)
                      ·
                        rfl

theorem cell23_239348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_239348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239348 prefixEnd_239348 := by exact prefixLift 239348
  have htrace : WordTrace (prefixWord ++ tailWord_239348) baseStart_239348 baseEnd_239348 := by
    simpa [prefixWord, tailWord_239348, baseEnd_239348] using wordTrace_append hprefix tailTrace_239348
  have hstable : (prefixWord ++ tailWord_239348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239348).length < 2 ^ (prefixWord ++ tailWord_239348).sum := by decide
  have hdescent : baseEnd_239348 < baseStart_239348 := by decide
  rcases family_descends (prefixWord ++ tailWord_239348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239358 : List Nat := [4, 2, 2, 1, 3, 2, 1, 1, 3, 4]
def baseStart_239358 : Nat := 118140960795 + 239358 * 2 ^ 59
def prefixEnd_239358 : Nat := 4983230072969 + 3 ^ 40 * 239358 * 2
def baseEnd_239358 : Nat := 40968567499659914808073

theorem tailTrace_239358 : CollatzResearch.WordTrace tailWord_239358 prefixEnd_239358 40968567499659914808073 := by
  unfold tailWord_239358
  simp only [CollatzResearch.WordTrace]
  refine ⟨1091262933356789992119841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5820068977902879957972485 1091262933356789992119841)
  ·
    refine ⟨818447200017592494089881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1091262933356789992119841 818447200017592494089881)
    ·
      refine ⟨613835400013194370567411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 818447200017592494089881 613835400013194370567411)
      ·
        refine ⟨920753100019791555851117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613835400013194370567411 920753100019791555851117)
        ·
          refine ⟨345282412507421833444169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 920753100019791555851117 345282412507421833444169)
          ·
            refine ⟨258961809380566375083127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345282412507421833444169 258961809380566375083127)
            ·
              refine ⟨388442714070849562624691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258961809380566375083127 388442714070849562624691)
              ·
                refine ⟨582664071106274343937037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 388442714070849562624691 582664071106274343937037)
                ·
                  refine ⟨218499026664852878976389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 582664071106274343937037 218499026664852878976389)
                  ·
                    refine ⟨40968567499659914808073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 218499026664852878976389 40968567499659914808073)
                    ·
                      rfl

theorem cell23_239358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_239358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239358 prefixEnd_239358 := by exact prefixLift 239358
  have htrace : WordTrace (prefixWord ++ tailWord_239358) baseStart_239358 baseEnd_239358 := by
    simpa [prefixWord, tailWord_239358, baseEnd_239358] using wordTrace_append hprefix tailTrace_239358
  have hstable : (prefixWord ++ tailWord_239358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239358).length < 2 ^ (prefixWord ++ tailWord_239358).sum := by decide
  have hdescent : baseEnd_239358 < baseStart_239358 := by decide
  rcases family_descends (prefixWord ++ tailWord_239358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239374 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2]
def baseStart_239374 : Nat := 118140960795 + 239374 * 2 ^ 59
def prefixEnd_239374 : Nat := 4983230072969 + 3 ^ 40 * 239374 * 2
def baseEnd_239374 : Nat := 122913918189451681824145

theorem tailTrace_239374 : CollatzResearch.WordTrace tailWord_239374 prefixEnd_239374 122913918189451681824145 := by
  unfold tailWord_239374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1091335879349544333692647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5820458023197569779694117 1091335879349544333692647)
  ·
    refine ⟨1637003819024316500538971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1091335879349544333692647 1637003819024316500538971)
    ·
      refine ⟨2455505728536474750808457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1637003819024316500538971 2455505728536474750808457)
      ·
        refine ⟨1841629296402356063106343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2455505728536474750808457 1841629296402356063106343)
        ·
          refine ⟨2762443944603534094659515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1841629296402356063106343 2762443944603534094659515)
          ·
            refine ⟨4143665916905301141989273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2762443944603534094659515 4143665916905301141989273)
            ·
              refine ⟨3107749437678975856491955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4143665916905301141989273 3107749437678975856491955)
              ·
                refine ⟨4661624156518463784737933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3107749437678975856491955 4661624156518463784737933)
                ·
                  refine ⟨1748109058694423919276725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4661624156518463784737933 1748109058694423919276725)
                  ·
                    refine ⟨163885224252602242432193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1748109058694423919276725 163885224252602242432193)
                    ·
                      refine ⟨122913918189451681824145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 163885224252602242432193 122913918189451681824145)
                      ·
                        rfl

theorem cell23_239374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2].length) (baseStart_239374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239374 prefixEnd_239374 := by exact prefixLift 239374
  have htrace : WordTrace (prefixWord ++ tailWord_239374) baseStart_239374 baseEnd_239374 := by
    simpa [prefixWord, tailWord_239374, baseEnd_239374] using wordTrace_append hprefix tailTrace_239374
  have hstable : (prefixWord ++ tailWord_239374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239374).length < 2 ^ (prefixWord ++ tailWord_239374).sum := by decide
  have hdescent : baseEnd_239374 < baseStart_239374 := by decide
  rcases family_descends (prefixWord ++ tailWord_239374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239384 : List Nat := [2, 1, 2, 3, 1, 1, 5, 2, 1, 5]
def baseStart_239384 : Nat := 118140960795 + 239384 * 2 ^ 59
def prefixEnd_239384 : Nat := 4983230072969 + 3 ^ 40 * 239384 * 2
def baseEnd_239384 : Nat := 40973017665332214233033

theorem tailTrace_239384 : CollatzResearch.WordTrace tailWord_239384 prefixEnd_239384 40973017665332214233033 := by
  unfold tailWord_239384
  simp only [CollatzResearch.WordTrace]
  refine ⟨4365525882380063188702603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5820701176506750918270137 4365525882380063188702603)
  ·
    refine ⟨6548288823570094783053905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4365525882380063188702603 6548288823570094783053905)
    ·
      refine ⟨4911216617677571087290429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6548288823570094783053905 4911216617677571087290429)
      ·
        refine ⟨1841706231629089157733911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4911216617677571087290429 1841706231629089157733911)
        ·
          refine ⟨2762559347443633736600867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1841706231629089157733911 2762559347443633736600867)
          ·
            refine ⟨4143839021165450604901301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2762559347443633736600867 4143839021165450604901301)
            ·
              refine ⟨388484908234260994209497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4143839021165450604901301 388484908234260994209497)
              ·
                refine ⟨291363681175695745657123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 388484908234260994209497 291363681175695745657123)
                ·
                  refine ⟨437045521763543618485685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 291363681175695745657123 437045521763543618485685)
                  ·
                    refine ⟨40973017665332214233033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 437045521763543618485685 40973017665332214233033)
                    ·
                      rfl

theorem cell23_239384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2, 1, 5].length) (baseStart_239384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239384 prefixEnd_239384 := by exact prefixLift 239384
  have htrace : WordTrace (prefixWord ++ tailWord_239384) baseStart_239384 baseEnd_239384 := by
    simpa [prefixWord, tailWord_239384, baseEnd_239384] using wordTrace_append hprefix tailTrace_239384
  have hstable : (prefixWord ++ tailWord_239384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239384).length < 2 ^ (prefixWord ++ tailWord_239384).sum := by decide
  have hdescent : baseEnd_239384 < baseStart_239384 := by decide
  rcases family_descends (prefixWord ++ tailWord_239384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239387 : List Nat := [1, 1, 1, 1, 1, 1, 4, 5, 3, 1, 4]
def baseStart_239387 : Nat := 118140960795 + 239387 * 2 ^ 59
def prefixEnd_239387 : Nat := 4983230072969 + 3 ^ 40 * 239387 * 2
def baseEnd_239387 : Nat := 122920593437960130961585

theorem tailTrace_239387 : CollatzResearch.WordTrace tailWord_239387 prefixEnd_239387 122920593437960130961585 := by
  unfold tailWord_239387
  simp only [CollatzResearch.WordTrace]
  refine ⟨8731161183749257889764415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5820774122499505259842943 8731161183749257889764415)
  ·
    refine ⟨13096741775623886834646623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8731161183749257889764415 13096741775623886834646623)
    ·
      refine ⟨19645112663435830251969935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13096741775623886834646623 19645112663435830251969935)
      ·
        refine ⟨29467668995153745377954903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19645112663435830251969935 29467668995153745377954903)
        ·
          refine ⟨44201503492730618066932355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29467668995153745377954903 44201503492730618066932355)
          ·
            refine ⟨66302255239095927100398533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44201503492730618066932355 66302255239095927100398533)
            ·
              refine ⟨12431672857330486331324725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66302255239095927100398533 12431672857330486331324725)
              ·
                refine ⟨1165469330374733093561693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12431672857330486331324725 1165469330374733093561693)
                ·
                  refine ⟨437050998890524910085635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1165469330374733093561693 437050998890524910085635)
                  ·
                    refine ⟨655576498335787365128453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 437050998890524910085635 655576498335787365128453)
                    ·
                      refine ⟨122920593437960130961585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 655576498335787365128453 122920593437960130961585)
                      ·
                        rfl

theorem cell23_239387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3, 1, 4].length) (baseStart_239387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239387 prefixEnd_239387 := by exact prefixLift 239387
  have htrace : WordTrace (prefixWord ++ tailWord_239387) baseStart_239387 baseEnd_239387 := by
    simpa [prefixWord, tailWord_239387, baseEnd_239387] using wordTrace_append hprefix tailTrace_239387
  have hstable : (prefixWord ++ tailWord_239387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239387).length < 2 ^ (prefixWord ++ tailWord_239387).sum := by decide
  have hdescent : baseEnd_239387 < baseStart_239387 := by decide
  rcases family_descends (prefixWord ++ tailWord_239387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239391 : List Nat := [1, 1, 2, 4, 2, 1, 4, 1, 2, 3, 2]
def baseStart_239391 : Nat := 118140960795 + 239391 * 2 ^ 59
def prefixEnd_239391 : Nat := 4983230072969 + 3 ^ 40 * 239391 * 2
def baseEnd_239391 : Nat := 122922647360578115311567

theorem tailTrace_239391 : CollatzResearch.WordTrace tailWord_239391 prefixEnd_239391 122922647360578115311567 := by
  unfold tailWord_239391
  simp only [CollatzResearch.WordTrace]
  refine ⟨8731307075734766572910027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5820871383823177715273351 8731307075734766572910027)
  ·
    refine ⟨13096960613602149859365041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8731307075734766572910027 13096960613602149859365041)
    ·
      refine ⟨9822720460201612394523781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13096960613602149859365041 9822720460201612394523781)
      ·
        refine ⟨1841760086287802323973209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9822720460201612394523781 1841760086287802323973209)
        ·
          refine ⟨1381320064715851742979907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1841760086287802323973209 1381320064715851742979907)
          ·
            refine ⟨2071980097073777614469861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1381320064715851742979907 2071980097073777614469861)
            ·
              refine ⟨388496268201333302713099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2071980097073777614469861 388496268201333302713099)
              ·
                refine ⟨582744402301999954069649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 388496268201333302713099 582744402301999954069649)
                ·
                  refine ⟨437058301726499965552237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 582744402301999954069649 437058301726499965552237)
                  ·
                    refine ⟨163896863147437487082089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 437058301726499965552237 163896863147437487082089)
                    ·
                      refine ⟨122922647360578115311567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 163896863147437487082089 122922647360578115311567)
                      ·
                        rfl

theorem cell23_239391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 2, 3, 2].length) (baseStart_239391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239391 prefixEnd_239391 := by exact prefixLift 239391
  have htrace : WordTrace (prefixWord ++ tailWord_239391) baseStart_239391 baseEnd_239391 := by
    simpa [prefixWord, tailWord_239391, baseEnd_239391] using wordTrace_append hprefix tailTrace_239391
  have hstable : (prefixWord ++ tailWord_239391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239391).length < 2 ^ (prefixWord ++ tailWord_239391).sum := by decide
  have hdescent : baseEnd_239391 < baseStart_239391 := by decide
  rcases family_descends (prefixWord ++ tailWord_239391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239397 : List Nat := [1, 3, 1, 2, 3, 2, 1, 1, 3, 6]
def baseStart_239397 : Nat := 118140960795 + 239397 * 2 ^ 59
def prefixEnd_239397 : Nat := 4983230072969 + 3 ^ 40 * 239397 * 2
def baseEnd_239397 : Nat := 40975242748168363945513

theorem tailTrace_239397 : CollatzResearch.WordTrace tailWord_239397 prefixEnd_239397 40975242748168363945513 := by
  unfold tailWord_239397
  simp only [CollatzResearch.WordTrace]
  refine ⟨8731525913713029597628445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5821017275808686398418963 8731525913713029597628445)
  ·
    refine ⟨3274322217642386099110667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8731525913713029597628445 3274322217642386099110667)
    ·
      refine ⟨4911483326463579148666001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3274322217642386099110667 4911483326463579148666001)
      ·
        refine ⟨3683612494847684361499501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4911483326463579148666001 3683612494847684361499501)
        ·
          refine ⟨1381354685567881635562313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3683612494847684361499501 1381354685567881635562313)
          ·
            refine ⟨1036016014175911226671735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1381354685567881635562313 1036016014175911226671735)
            ·
              refine ⟨1554024021263866840007603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1036016014175911226671735 1554024021263866840007603)
              ·
                refine ⟨2331036031895800260011405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1554024021263866840007603 2331036031895800260011405)
                ·
                  refine ⟨874138511960925097504277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2331036031895800260011405 874138511960925097504277)
                  ·
                    refine ⟨40975242748168363945513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 874138511960925097504277 40975242748168363945513)
                    ·
                      rfl

theorem cell23_239397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 6].length) (baseStart_239397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239397 prefixEnd_239397 := by exact prefixLift 239397
  have htrace : WordTrace (prefixWord ++ tailWord_239397) baseStart_239397 baseEnd_239397 := by
    simpa [prefixWord, tailWord_239397, baseEnd_239397] using wordTrace_append hprefix tailTrace_239397
  have hstable : (prefixWord ++ tailWord_239397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239397).length < 2 ^ (prefixWord ++ tailWord_239397).sum := by decide
  have hdescent : baseEnd_239397 < baseStart_239397 := by decide
  rcases family_descends (prefixWord ++ tailWord_239397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239427 : List Nat := [1, 1, 1, 3, 1, 5, 3, 8]
def baseStart_239427 : Nat := 118140960795 + 239427 * 2 ^ 59
def prefixEnd_239427 : Nat := 4983230072969 + 3 ^ 40 * 239427 * 2
def baseEnd_239427 : Nat := 4553375283857036091163

theorem tailTrace_239427 : CollatzResearch.WordTrace tailWord_239427 prefixEnd_239427 4553375283857036091163 := by
  unfold tailWord_239427
  simp only [CollatzResearch.WordTrace]
  refine ⟨8732620103604344721220535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5821746735736229814147023 8732620103604344721220535)
  ·
    refine ⟨13098930155406517081830803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8732620103604344721220535 13098930155406517081830803)
    ·
      refine ⟨19648395233109775622746205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13098930155406517081830803 19648395233109775622746205)
      ·
        refine ⟨7368148212416165858529827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19648395233109775622746205 7368148212416165858529827)
        ·
          refine ⟨11052222318624248787794741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7368148212416165858529827 11052222318624248787794741)
          ·
            refine ⟨1036145842371023323855757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11052222318624248787794741 1036145842371023323855757)
            ·
              refine ⟨388554690889133746445909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1036145842371023323855757 388554690889133746445909)
              ·
                refine ⟨4553375283857036091163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 388554690889133746445909 4553375283857036091163)
                ·
                  rfl

theorem cell23_239427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 8].length) (baseStart_239427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239427 prefixEnd_239427 := by exact prefixLift 239427
  have htrace : WordTrace (prefixWord ++ tailWord_239427) baseStart_239427 baseEnd_239427 := by
    simpa [prefixWord, tailWord_239427, baseEnd_239427] using wordTrace_append hprefix tailTrace_239427
  have hstable : (prefixWord ++ tailWord_239427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239427).length < 2 ^ (prefixWord ++ tailWord_239427).sum := by decide
  have hdescent : baseEnd_239427 < baseStart_239427 := by decide
  rcases family_descends (prefixWord ++ tailWord_239427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239434 : List Nat := [3, 1, 2, 1, 1, 1, 6, 1, 1, 2, 4]
def baseStart_239434 : Nat := 118140960795 + 239434 * 2 ^ 59
def prefixEnd_239434 : Nat := 4983230072969 + 3 ^ 40 * 239434 * 2
def baseEnd_239434 : Nat := 122944727028721447073869

theorem tailTrace_239434 : CollatzResearch.WordTrace tailWord_239434 prefixEnd_239434 122944727028721447073869 := by
  unfold tailWord_239434
  simp only [CollatzResearch.WordTrace]
  refine ⟨2183218853644746229181339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5821916943052656611150237 2183218853644746229181339)
  ·
    refine ⟨3274828280467119343772009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2183218853644746229181339 3274828280467119343772009)
    ·
      refine ⟨2456121210350339507829007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3274828280467119343772009 2456121210350339507829007)
      ·
        refine ⟨3684181815525509261743511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2456121210350339507829007 3684181815525509261743511)
        ·
          refine ⟨5526272723288263892615267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3684181815525509261743511 5526272723288263892615267)
          ·
            refine ⟨8289409084932395838922901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5526272723288263892615267 8289409084932395838922901)
            ·
              refine ⟨388566050856206054949511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8289409084932395838922901 388566050856206054949511)
              ·
                refine ⟨582849076284309082424267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 388566050856206054949511 582849076284309082424267)
                ·
                  refine ⟨874273614426463623636401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 582849076284309082424267 874273614426463623636401)
                  ·
                    refine ⟨655705210819847717727301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 874273614426463623636401 655705210819847717727301)
                    ·
                      refine ⟨122944727028721447073869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 655705210819847717727301 122944727028721447073869)
                      ·
                        rfl

theorem cell23_239434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 1, 2, 4].length) (baseStart_239434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239434 prefixEnd_239434 := by exact prefixLift 239434
  have htrace : WordTrace (prefixWord ++ tailWord_239434) baseStart_239434 baseEnd_239434 := by
    simpa [prefixWord, tailWord_239434, baseEnd_239434] using wordTrace_append hprefix tailTrace_239434
  have hstable : (prefixWord ++ tailWord_239434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239434).length < 2 ^ (prefixWord ++ tailWord_239434).sum := by decide
  have hdescent : baseEnd_239434 < baseStart_239434 := by decide
  rcases family_descends (prefixWord ++ tailWord_239434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239455 : List Nat := [1, 1, 2, 3, 1, 5, 2, 3, 1, 2, 2]
def baseStart_239455 : Nat := 118140960795 + 239455 * 2 ^ 59
def prefixEnd_239455 : Nat := 4983230072969 + 3 ^ 40 * 239455 * 2
def baseEnd_239455 : Nat := 122955510122465864911273

theorem tailTrace_239455 : CollatzResearch.WordTrace tailWord_239455 prefixEnd_239455 122955510122465864911273 := by
  unfold tailWord_239455
  simp only [CollatzResearch.WordTrace]
  refine ⟨8733641347502905503239819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5822427565001937002159879 8733641347502905503239819)
  ·
    refine ⟨13100462021254358254859729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8733641347502905503239819 13100462021254358254859729)
    ·
      refine ⟨9825346515940768691144797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13100462021254358254859729 9825346515940768691144797)
      ·
        refine ⟨3684504943477788259179299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9825346515940768691144797 3684504943477788259179299)
        ·
          refine ⟨5526757415216682388768949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3684504943477788259179299 5526757415216682388768949)
          ·
            refine ⟨518133507676563973947089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5526757415216682388768949 518133507676563973947089)
            ·
              refine ⟨388600130757422980460317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 518133507676563973947089 388600130757422980460317)
              ·
                refine ⟨145725049034033617672619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 388600130757422980460317 145725049034033617672619)
                ·
                  refine ⟨218587573551050426508929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145725049034033617672619 218587573551050426508929)
                  ·
                    refine ⟨163940680163287819881697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 218587573551050426508929 163940680163287819881697)
                    ·
                      refine ⟨122955510122465864911273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 163940680163287819881697 122955510122465864911273)
                      ·
                        rfl

theorem cell23_239455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 3, 1, 2, 2].length) (baseStart_239455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239455 prefixEnd_239455 := by exact prefixLift 239455
  have htrace : WordTrace (prefixWord ++ tailWord_239455) baseStart_239455 baseEnd_239455 := by
    simpa [prefixWord, tailWord_239455, baseEnd_239455] using wordTrace_append hprefix tailTrace_239455
  have hstable : (prefixWord ++ tailWord_239455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239455).length < 2 ^ (prefixWord ++ tailWord_239455).sum := by decide
  have hdescent : baseEnd_239455 < baseStart_239455 := by decide
  rcases family_descends (prefixWord ++ tailWord_239455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239458 : List Nat := [3, 3, 2, 1, 2, 2, 1, 3, 1, 2, 3]
def baseStart_239458 : Nat := 118140960795 + 239458 * 2 ^ 59
def prefixEnd_239458 : Nat := 4983230072969 + 3 ^ 40 * 239458 * 2
def baseEnd_239458 : Nat := 122957050564429353173759

theorem tailTrace_239458 : CollatzResearch.WordTrace tailWord_239458 prefixEnd_239458 122957050564429353173759 := by
  unfold tailWord_239458
  simp only [CollatzResearch.WordTrace]
  refine ⟨2183437691623009253899757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5822500510994691343732685 2183437691623009253899757)
  ·
    refine ⟨818789134358628470212409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2183437691623009253899757 818789134358628470212409)
    ·
      refine ⟨614091850768971352659307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 818789134358628470212409 614091850768971352659307)
      ·
        refine ⟨921137776153457028988961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614091850768971352659307 921137776153457028988961)
        ·
          refine ⟨690853332115092771741721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 921137776153457028988961 690853332115092771741721)
          ·
            refine ⟨518139999086319578806291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 690853332115092771741721 518139999086319578806291)
            ·
              refine ⟨777209998629479368209437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518139999086319578806291 777209998629479368209437)
              ·
                refine ⟨291453749486054763078539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 777209998629479368209437 291453749486054763078539)
                ·
                  refine ⟨437180624229082144617809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 291453749486054763078539 437180624229082144617809)
                  ·
                    refine ⟨327885468171811608463357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 437180624229082144617809 327885468171811608463357)
                    ·
                      refine ⟨122957050564429353173759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 327885468171811608463357 122957050564429353173759)
                      ·
                        rfl

theorem cell23_239458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_239458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239458 prefixEnd_239458 := by exact prefixLift 239458
  have htrace : WordTrace (prefixWord ++ tailWord_239458) baseStart_239458 baseEnd_239458 := by
    simpa [prefixWord, tailWord_239458, baseEnd_239458] using wordTrace_append hprefix tailTrace_239458
  have hstable : (prefixWord ++ tailWord_239458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239458).length < 2 ^ (prefixWord ++ tailWord_239458).sum := by decide
  have hdescent : baseEnd_239458 < baseStart_239458 := by decide
  rcases family_descends (prefixWord ++ tailWord_239458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239488 : List Nat := [2, 1, 1, 2, 1, 2, 7, 1, 2, 1, 3]
def baseStart_239488 : Nat := 118140960795 + 239488 * 2 ^ 59
def prefixEnd_239488 : Nat := 4983230072969 + 3 ^ 40 * 239488 * 2
def baseEnd_239488 : Nat := 122972454984064235798621

theorem tailTrace_239488 : CollatzResearch.WordTrace tailWord_239488 prefixEnd_239488 122972454984064235798621 := by
  unfold tailWord_239488
  simp only [CollatzResearch.WordTrace]
  refine ⟨4367422478191676069595559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5823229970922234759460745 4367422478191676069595559)
  ·
    refine ⟨6551133717287514104393339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4367422478191676069595559 6551133717287514104393339)
    ·
      refine ⟨9826700575931271156590009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6551133717287514104393339 9826700575931271156590009)
      ·
        refine ⟨7370025431948453367442507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9826700575931271156590009 7370025431948453367442507)
        ·
          refine ⟨11055038147922680051163761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7370025431948453367442507 11055038147922680051163761)
          ·
            refine ⟨8291278610942010038372821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11055038147922680051163761 8291278610942010038372821)
            ·
              refine ⟨194326842443953360274363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 8291278610942010038372821 194326842443953360274363)
              ·
                refine ⟨291490263665930040411545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194326842443953360274363 291490263665930040411545)
                ·
                  refine ⟨218617697749447530308659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 291490263665930040411545 218617697749447530308659)
                  ·
                    refine ⟨327926546624171295462989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 218617697749447530308659 327926546624171295462989)
                    ·
                      refine ⟨122972454984064235798621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 327926546624171295462989 122972454984064235798621)
                      ·
                        rfl

theorem cell23_239488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 1, 2, 1, 3].length) (baseStart_239488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239488 prefixEnd_239488 := by exact prefixLift 239488
  have htrace : WordTrace (prefixWord ++ tailWord_239488) baseStart_239488 baseEnd_239488 := by
    simpa [prefixWord, tailWord_239488, baseEnd_239488] using wordTrace_append hprefix tailTrace_239488
  have hstable : (prefixWord ++ tailWord_239488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239488).length < 2 ^ (prefixWord ++ tailWord_239488).sum := by decide
  have hdescent : baseEnd_239488 < baseStart_239488 := by decide
  rcases family_descends (prefixWord ++ tailWord_239488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239514 : List Nat := [3, 1, 1, 4, 2, 1, 1, 1, 1, 3, 5]
def baseStart_239514 : Nat := 118140960795 + 239514 * 2 ^ 59
def prefixEnd_239514 : Nat := 4983230072969 + 3 ^ 40 * 239514 * 2
def baseEnd_239514 : Nat := 122985805481081134073501

theorem tailTrace_239514 : CollatzResearch.WordTrace tailWord_239514 prefixEnd_239514 122985805481081134073501 := by
  unfold tailWord_239514
  simp only [CollatzResearch.WordTrace]
  refine ⟨2183948313572289644909399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5823862169526105719758397 2183948313572289644909399)
  ·
    refine ⟨3275922470358434467364099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2183948313572289644909399 3275922470358434467364099)
    ·
      refine ⟨4913883705537651701046149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3275922470358434467364099 4913883705537651701046149)
      ·
        refine ⟨921353194788309693946153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4913883705537651701046149 921353194788309693946153)
        ·
          refine ⟨691014896091232270459615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 921353194788309693946153 691014896091232270459615)
          ·
            refine ⟨1036522344136848405689423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 691014896091232270459615 1036522344136848405689423)
            ·
              refine ⟨1554783516205272608534135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1036522344136848405689423 1554783516205272608534135)
              ·
                refine ⟨2332175274307908912801203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1554783516205272608534135 2332175274307908912801203)
                ·
                  refine ⟨3498262911461863369201805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2332175274307908912801203 3498262911461863369201805)
                  ·
                    refine ⟨1311848591798198763450677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3498262911461863369201805 1311848591798198763450677)
                    ·
                      refine ⟨122985805481081134073501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1311848591798198763450677 122985805481081134073501)
                      ·
                        rfl

theorem cell23_239514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_239514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239514 prefixEnd_239514 := by exact prefixLift 239514
  have htrace : WordTrace (prefixWord ++ tailWord_239514) baseStart_239514 baseEnd_239514 := by
    simpa [prefixWord, tailWord_239514, baseEnd_239514] using wordTrace_append hprefix tailTrace_239514
  have hstable : (prefixWord ++ tailWord_239514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239514).length < 2 ^ (prefixWord ++ tailWord_239514).sum := by decide
  have hdescent : baseEnd_239514 < baseStart_239514 := by decide
  rcases family_descends (prefixWord ++ tailWord_239514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239544 : List Nat := [2, 1, 2, 1, 2, 3, 2, 1, 1, 5, 3]
def baseStart_239544 : Nat := 118140960795 + 239544 * 2 ^ 59
def prefixEnd_239544 : Nat := 4983230072969 + 3 ^ 40 * 239544 * 2
def baseEnd_239544 : Nat := 123001209900716016698363

theorem tailTrace_239544 : CollatzResearch.WordTrace tailWord_239544 prefixEnd_239544 123001209900716016698363 := by
  unfold tailWord_239544
  simp only [CollatzResearch.WordTrace]
  refine ⟨4368443722090236851614843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5824591629453649135486457 4368443722090236851614843)
  ·
    refine ⟨6552665583135355277422265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4368443722090236851614843 6552665583135355277422265)
    ·
      refine ⟨4914499187351516458066699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6552665583135355277422265 4914499187351516458066699)
      ·
        refine ⟨7371748781027274687100049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4914499187351516458066699 7371748781027274687100049)
        ·
          refine ⟨5528811585770456015325037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7371748781027274687100049 5528811585770456015325037)
          ·
            refine ⟨2073304344663921005746889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5528811585770456015325037 2073304344663921005746889)
            ·
              refine ⟨1554978258497940754310167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2073304344663921005746889 1554978258497940754310167)
              ·
                refine ⟨2332467387746911131465251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1554978258497940754310167 2332467387746911131465251)
                ·
                  refine ⟨3498701081620366697197877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2332467387746911131465251 3498701081620366697197877)
                  ·
                    refine ⟨328003226401909377862301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3498701081620366697197877 328003226401909377862301)
                    ·
                      refine ⟨123001209900716016698363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 328003226401909377862301 123001209900716016698363)
                      ·
                        rfl

theorem cell23_239544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 1, 5, 3].length) (baseStart_239544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239544 prefixEnd_239544 := by exact prefixLift 239544
  have htrace : WordTrace (prefixWord ++ tailWord_239544) baseStart_239544 baseEnd_239544 := by
    simpa [prefixWord, tailWord_239544, baseEnd_239544] using wordTrace_append hprefix tailTrace_239544
  have hstable : (prefixWord ++ tailWord_239544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239544).length < 2 ^ (prefixWord ++ tailWord_239544).sum := by decide
  have hdescent : baseEnd_239544 < baseStart_239544 := by decide
  rcases family_descends (prefixWord ++ tailWord_239544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239621 : List Nat := [1, 3, 1, 1, 2, 5, 1, 1, 1, 4, 3]
def baseStart_239621 : Nat := 118140960795 + 239621 * 2 ^ 59
def prefixEnd_239621 : Nat := 4983230072969 + 3 ^ 40 * 239621 * 2
def baseEnd_239621 : Nat := 123040747911112215435509

theorem tailTrace_239621 : CollatzResearch.WordTrace tailWord_239621 prefixEnd_239621 123040747911112215435509 := by
  unfold tailWord_239621
  simp only [CollatzResearch.WordTrace]
  refine ⟨8739695864901515853782717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5826463909934343902521811 8739695864901515853782717)
  ·
    refine ⟨3277385949338068445168519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8739695864901515853782717 3277385949338068445168519)
    ·
      refine ⟨4916078924007102667752779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3277385949338068445168519 4916078924007102667752779)
      ·
        refine ⟨7374118386010654001629169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4916078924007102667752779 7374118386010654001629169)
        ·
          refine ⟨5530588789507990501221877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7374118386010654001629169 5530588789507990501221877)
          ·
            refine ⟨518492699016374109489551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5530588789507990501221877 518492699016374109489551)
            ·
              refine ⟨777739048524561164234327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518492699016374109489551 777739048524561164234327)
              ·
                refine ⟨1166608572786841746351491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 777739048524561164234327 1166608572786841746351491)
                ·
                  refine ⟨1749912859180262619527237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1166608572786841746351491 1749912859180262619527237)
                  ·
                    refine ⟨328108661096299241161357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1749912859180262619527237 328108661096299241161357)
                    ·
                      refine ⟨123040747911112215435509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 328108661096299241161357 123040747911112215435509)
                      ·
                        rfl

theorem cell23_239621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 4, 3].length) (baseStart_239621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239621 prefixEnd_239621 := by exact prefixLift 239621
  have htrace : WordTrace (prefixWord ++ tailWord_239621) baseStart_239621 baseEnd_239621 := by
    simpa [prefixWord, tailWord_239621, baseEnd_239621] using wordTrace_append hprefix tailTrace_239621
  have hstable : (prefixWord ++ tailWord_239621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239621).length < 2 ^ (prefixWord ++ tailWord_239621).sum := by decide
  have hdescent : baseEnd_239621 < baseStart_239621 := by decide
  rcases family_descends (prefixWord ++ tailWord_239621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239624 : List Nat := [2, 1, 3, 2, 1, 2, 2, 2, 8]
def baseStart_239624 : Nat := 118140960795 + 239624 * 2 ^ 59
def prefixEnd_239624 : Nat := 4983230072969 + 3 ^ 40 * 239624 * 2
def baseEnd_239624 : Nat := 13671365372563967077555

theorem tailTrace_239624 : CollatzResearch.WordTrace tailWord_239624 prefixEnd_239624 13671365372563967077555 := by
  unfold tailWord_239624
  simp only [CollatzResearch.WordTrace]
  refine ⟨4369902641945323683070963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5826536855927098244094617 4369902641945323683070963)
  ·
    refine ⟨6554853962917985524606445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4369902641945323683070963 6554853962917985524606445)
    ·
      refine ⟨2458070236094244571727417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6554853962917985524606445 2458070236094244571727417)
      ·
        refine ⟨1843552677070683428795563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2458070236094244571727417 1843552677070683428795563)
        ·
          refine ⟨2765329015606025143193345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1843552677070683428795563 2765329015606025143193345)
          ·
            refine ⟨2073996761704518857395009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2765329015606025143193345 2073996761704518857395009)
            ·
              refine ⟨1555497571278389143046257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2073996761704518857395009 1555497571278389143046257)
              ·
                refine ⟨1166623178458791857284693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1555497571278389143046257 1166623178458791857284693)
                ·
                  refine ⟨13671365372563967077555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1166623178458791857284693 13671365372563967077555)
                  ·
                    rfl

theorem cell23_239624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 8].length) (baseStart_239624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239624 prefixEnd_239624 := by exact prefixLift 239624
  have htrace : WordTrace (prefixWord ++ tailWord_239624) baseStart_239624 baseEnd_239624 := by
    simpa [prefixWord, tailWord_239624, baseEnd_239624] using wordTrace_append hprefix tailTrace_239624
  have hstable : (prefixWord ++ tailWord_239624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239624).length < 2 ^ (prefixWord ++ tailWord_239624).sum := by decide
  have hdescent : baseEnd_239624 < baseStart_239624 := by decide
  rcases family_descends (prefixWord ++ tailWord_239624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239645 : List Nat := [1, 4, 2, 2, 2, 1, 2, 4, 1, 4]
def baseStart_239645 : Nat := 118140960795 + 239645 * 2 ^ 59
def prefixEnd_239645 : Nat := 4983230072969 + 3 ^ 40 * 239645 * 2
def baseEnd_239645 : Nat := 41017690482273373845133

theorem tailTrace_239645 : CollatzResearch.WordTrace tailWord_239645 prefixEnd_239645 41017690482273373845133 := by
  unfold tailWord_239645
  simp only [CollatzResearch.WordTrace]
  refine ⟨8740571216814567952656389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5827047477876378635104259 8740571216814567952656389)
  ·
    refine ⟨1638857103152731491123073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8740571216814567952656389 1638857103152731491123073)
    ·
      refine ⟨1229142827364548618342305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1638857103152731491123073 1229142827364548618342305)
      ·
        refine ⟨921857120523411463756729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1229142827364548618342305 921857120523411463756729)
        ·
          refine ⟨691392840392558597817547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 921857120523411463756729 691392840392558597817547)
          ·
            refine ⟨1037089260588837896726321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 691392840392558597817547 1037089260588837896726321)
            ·
              refine ⟨777816945441628422544741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1037089260588837896726321 777816945441628422544741)
              ·
                refine ⟨145840677270305329227139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 777816945441628422544741 145840677270305329227139)
                ·
                  refine ⟨218761015905457993840709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145840677270305329227139 218761015905457993840709)
                  ·
                    refine ⟨41017690482273373845133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 218761015905457993840709 41017690482273373845133)
                    ·
                      rfl

theorem cell23_239645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_239645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239645 prefixEnd_239645 := by exact prefixLift 239645
  have htrace : WordTrace (prefixWord ++ tailWord_239645) baseStart_239645 baseEnd_239645 := by
    simpa [prefixWord, tailWord_239645, baseEnd_239645] using wordTrace_append hprefix tailTrace_239645
  have hstable : (prefixWord ++ tailWord_239645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239645).length < 2 ^ (prefixWord ++ tailWord_239645).sum := by decide
  have hdescent : baseEnd_239645 < baseStart_239645 := by decide
  rcases family_descends (prefixWord ++ tailWord_239645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239671 : List Nat := [1, 1, 3, 1, 2, 2, 3, 4, 1, 5]
def baseStart_239671 : Nat := 118140960795 + 239671 * 2 ^ 59
def prefixEnd_239671 : Nat := 4983230072969 + 3 ^ 40 * 239671 * 2
def baseEnd_239671 : Nat := 41022140647945673270093

theorem tailTrace_239671 : CollatzResearch.WordTrace tailWord_239671 prefixEnd_239671 41022140647945673270093 := by
  unfold tailWord_239671
  simp only [CollatzResearch.WordTrace]
  refine ⟨8741519514720374393102867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5827679676480249595401911 8741519514720374393102867)
  ·
    refine ⟨13112279272080561589654301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8741519514720374393102867 13112279272080561589654301)
    ·
      refine ⟨4917104727030210596120363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13112279272080561589654301 4917104727030210596120363)
      ·
        refine ⟨7375657090545315894180545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4917104727030210596120363 7375657090545315894180545)
        ·
          refine ⟨5531742817908986920635409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7375657090545315894180545 5531742817908986920635409)
          ·
            refine ⟨4148807113431740190476557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5531742817908986920635409 4148807113431740190476557)
            ·
              refine ⟨1555802667536902571428709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4148807113431740190476557 1555802667536902571428709)
              ·
                refine ⟨291713000163169232142883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1555802667536902571428709 291713000163169232142883)
                ·
                  refine ⟨437569500244753848214325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 291713000163169232142883 437569500244753848214325)
                  ·
                    refine ⟨41022140647945673270093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 437569500244753848214325 41022140647945673270093)
                    ·
                      rfl

theorem cell23_239671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4, 1, 5].length) (baseStart_239671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239671 prefixEnd_239671 := by exact prefixLift 239671
  have htrace : WordTrace (prefixWord ++ tailWord_239671) baseStart_239671 baseEnd_239671 := by
    simpa [prefixWord, tailWord_239671, baseEnd_239671] using wordTrace_append hprefix tailTrace_239671
  have hstable : (prefixWord ++ tailWord_239671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239671).length < 2 ^ (prefixWord ++ tailWord_239671).sum := by decide
  have hdescent : baseEnd_239671 < baseStart_239671 := by decide
  rcases family_descends (prefixWord ++ tailWord_239671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239691 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 1, 8, 2]
def baseStart_239691 : Nat := 118140960795 + 239691 * 2 ^ 59
def prefixEnd_239691 : Nat := 4983230072969 + 3 ^ 40 * 239691 * 2
def baseEnd_239691 : Nat := 123076691556926941560187

theorem tailTrace_239691 : CollatzResearch.WordTrace tailWord_239691 prefixEnd_239691 123076691556926941560187 := by
  unfold tailWord_239691
  simp only [CollatzResearch.WordTrace]
  refine ⟨8742248974647917808830927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5828165983098611872553951 8742248974647917808830927)
  ·
    refine ⟨13113373461971876713246391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8742248974647917808830927 13113373461971876713246391)
    ·
      refine ⟨19670060192957815069869587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13113373461971876713246391 19670060192957815069869587)
      ·
        refine ⟨29505090289436722604804381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19670060192957815069869587 29505090289436722604804381)
        ·
          refine ⟨11064408858538770976801643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29505090289436722604804381 11064408858538770976801643)
          ·
            refine ⟨16596613287808156465202465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11064408858538770976801643 16596613287808156465202465)
            ·
              refine ⟨12447459965856117348901849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16596613287808156465202465 12447459965856117348901849)
              ·
                refine ⟨9335594974392088011676387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12447459965856117348901849 9335594974392088011676387)
                ·
                  refine ⟨14003392461588132017514581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9335594974392088011676387 14003392461588132017514581)
                  ·
                    refine ⟨164102255409235922080249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 14003392461588132017514581 164102255409235922080249)
                    ·
                      refine ⟨123076691556926941560187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 164102255409235922080249 123076691556926941560187)
                      ·
                        rfl

theorem cell23_239691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 8, 2].length) (baseStart_239691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239691 prefixEnd_239691 := by exact prefixLift 239691
  have htrace : WordTrace (prefixWord ++ tailWord_239691) baseStart_239691 baseEnd_239691 := by
    simpa [prefixWord, tailWord_239691, baseEnd_239691] using wordTrace_append hprefix tailTrace_239691
  have hstable : (prefixWord ++ tailWord_239691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239691).length < 2 ^ (prefixWord ++ tailWord_239691).sum := by decide
  have hdescent : baseEnd_239691 < baseStart_239691 := by decide
  rcases family_descends (prefixWord ++ tailWord_239691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239721 : List Nat := [1, 2, 1, 1, 1, 5, 2, 3, 1, 2, 4]
def baseStart_239721 : Nat := 118140960795 + 239721 * 2 ^ 59
def prefixEnd_239721 : Nat := 4983230072969 + 3 ^ 40 * 239721 * 2
def baseEnd_239721 : Nat := 123092095976561824185049

theorem tailTrace_239721 : CollatzResearch.WordTrace tailWord_239721 prefixEnd_239721 123092095976561824185049 := by
  unfold tailWord_239721
  simp only [CollatzResearch.WordTrace]
  refine ⟨8743343164539232932423017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5828895443026155288282011 8743343164539232932423017)
  ·
    refine ⟨6557507373404424699317263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8743343164539232932423017 6557507373404424699317263)
    ·
      refine ⟨9836261060106637048975895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6557507373404424699317263 9836261060106637048975895)
      ·
        refine ⟨14754391590159955573463843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9836261060106637048975895 14754391590159955573463843)
        ·
          refine ⟨22131587385239933360195765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14754391590159955573463843 22131587385239933360195765)
          ·
            refine ⟨2074836317366243752518353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22131587385239933360195765 2074836317366243752518353)
            ·
              refine ⟨1556127238024682814388765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2074836317366243752518353 1556127238024682814388765)
              ·
                refine ⟨583547714259256055395787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1556127238024682814388765 583547714259256055395787)
                ·
                  refine ⟨875321571388884083093681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 583547714259256055395787 875321571388884083093681)
                  ·
                    refine ⟨656491178541663062320261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 875321571388884083093681 656491178541663062320261)
                    ·
                      refine ⟨123092095976561824185049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 656491178541663062320261 123092095976561824185049)
                      ·
                        rfl

theorem cell23_239721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 2, 4].length) (baseStart_239721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239721 prefixEnd_239721 := by exact prefixLift 239721
  have htrace : WordTrace (prefixWord ++ tailWord_239721) baseStart_239721 baseEnd_239721 := by
    simpa [prefixWord, tailWord_239721, baseEnd_239721] using wordTrace_append hprefix tailTrace_239721
  have hstable : (prefixWord ++ tailWord_239721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239721).length < 2 ^ (prefixWord ++ tailWord_239721).sum := by decide
  have hdescent : baseEnd_239721 < baseStart_239721 := by decide
  rcases family_descends (prefixWord ++ tailWord_239721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239722 : List Nat := [3, 1, 3, 2, 4, 1, 1, 2, 1, 5]
def baseStart_239722 : Nat := 118140960795 + 239722 * 2 ^ 59
def prefixEnd_239722 : Nat := 4983230072969 + 3 ^ 40 * 239722 * 2
def baseEnd_239722 : Nat := 41030869819072106757515

theorem tailTrace_239722 : CollatzResearch.WordTrace tailWord_239722 prefixEnd_239722 41030869819072106757515 := by
  unfold tailWord_239722
  simp only [CollatzResearch.WordTrace]
  refine ⟨2185844909383902525802355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5828919758357073402139613 2185844909383902525802355)
  ·
    refine ⟨3278767364075853788703533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2185844909383902525802355 3278767364075853788703533)
    ·
      refine ⟨1229537761528445170763825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3278767364075853788703533 1229537761528445170763825)
      ·
        refine ⟨922153321146333878072869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1229537761528445170763825 922153321146333878072869)
        ·
          refine ⟨172903747714937602138663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 922153321146333878072869 172903747714937602138663)
          ·
            refine ⟨259355621572406403207995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172903747714937602138663 259355621572406403207995)
            ·
              refine ⟨389033432358609604811993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259355621572406403207995 389033432358609604811993)
              ·
                refine ⟨291775074268957203608995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 389033432358609604811993 291775074268957203608995)
                ·
                  refine ⟨437662611403435805413493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 291775074268957203608995 437662611403435805413493)
                  ·
                    refine ⟨41030869819072106757515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 437662611403435805413493 41030869819072106757515)
                    ·
                      rfl

theorem cell23_239722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_239722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239722 prefixEnd_239722 := by exact prefixLift 239722
  have htrace : WordTrace (prefixWord ++ tailWord_239722) baseStart_239722 baseEnd_239722 := by
    simpa [prefixWord, tailWord_239722, baseEnd_239722] using wordTrace_append hprefix tailTrace_239722
  have hstable : (prefixWord ++ tailWord_239722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239722).length < 2 ^ (prefixWord ++ tailWord_239722).sum := by decide
  have hdescent : baseEnd_239722 < baseStart_239722 := by decide
  rcases family_descends (prefixWord ++ tailWord_239722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239725 : List Nat := [1, 5, 1, 1, 2, 1, 2, 1, 5, 2, 2]
def baseStart_239725 : Nat := 118140960795 + 239725 * 2 ^ 59
def prefixEnd_239725 : Nat := 4983230072969 + 3 ^ 40 * 239725 * 2
def baseEnd_239725 : Nat := 123094149899179808535031

theorem tailTrace_239725 : CollatzResearch.WordTrace tailWord_239725 prefixEnd_239725 123094149899179808535031 := by
  unfold tailWord_239725
  simp only [CollatzResearch.WordTrace]
  refine ⟨8743489056524741615568629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5828992704349827743712419 8743489056524741615568629)
  ·
    refine ⟨819702099049194526459559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8743489056524741615568629 819702099049194526459559)
    ·
      refine ⟨1229553148573791789689339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 819702099049194526459559 1229553148573791789689339)
      ·
        refine ⟨1844329722860687684534009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1229553148573791789689339 1844329722860687684534009)
        ·
          refine ⟨1383247292145515763400507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1844329722860687684534009 1383247292145515763400507)
          ·
            refine ⟨2074870938218273645100761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1383247292145515763400507 2074870938218273645100761)
            ·
              refine ⟨1556153203663705233825571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2074870938218273645100761 1556153203663705233825571)
              ·
                refine ⟨2334229805495557850738357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1556153203663705233825571 2334229805495557850738357)
                ·
                  refine ⟨218834044265208548506721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2334229805495557850738357 218834044265208548506721)
                  ·
                    refine ⟨164125533198906411380041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 218834044265208548506721 164125533198906411380041)
                    ·
                      refine ⟨123094149899179808535031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 164125533198906411380041 123094149899179808535031)
                      ·
                        rfl

theorem cell23_239725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 5, 2, 2].length) (baseStart_239725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239725 prefixEnd_239725 := by exact prefixLift 239725
  have htrace : WordTrace (prefixWord ++ tailWord_239725) baseStart_239725 baseEnd_239725 := by
    simpa [prefixWord, tailWord_239725, baseEnd_239725] using wordTrace_append hprefix tailTrace_239725
  have hstable : (prefixWord ++ tailWord_239725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239725).length < 2 ^ (prefixWord ++ tailWord_239725).sum := by decide
  have hdescent : baseEnd_239725 < baseStart_239725 := by decide
  rcases family_descends (prefixWord ++ tailWord_239725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239728 : List Nat := [2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 3]
def baseStart_239728 : Nat := 118140960795 + 239728 * 2 ^ 59
def prefixEnd_239728 : Nat := 4983230072969 + 3 ^ 40 * 239728 * 2
def baseEnd_239728 : Nat := 123095690341143296797517

theorem tailTrace_239728 : CollatzResearch.WordTrace tailWord_239728 prefixEnd_239728 123095690341143296797517 := by
  unfold tailWord_239728
  simp only [CollatzResearch.WordTrace]
  refine ⟨4371799237756936563963919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5829065650342582085285225 4371799237756936563963919)
  ·
    refine ⟨6557698856635404845945879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4371799237756936563963919 6557698856635404845945879)
    ·
      refine ⟨9836548284953107268918819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6557698856635404845945879 9836548284953107268918819)
      ·
        refine ⟨14754822427429660903378229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9836548284953107268918819 14754822427429660903378229)
        ·
          refine ⟨1383264602571530709691709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14754822427429660903378229 1383264602571530709691709)
          ·
            refine ⟨518724225964324016134391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1383264602571530709691709 518724225964324016134391)
            ·
              refine ⟨778086338946486024201587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518724225964324016134391 778086338946486024201587)
              ·
                refine ⟨1167129508419729036302381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 778086338946486024201587 1167129508419729036302381)
                ·
                  refine ⟨437673565657398388613393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1167129508419729036302381 437673565657398388613393)
                  ·
                    refine ⟨328255174243048791460045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 437673565657398388613393 328255174243048791460045)
                    ·
                      refine ⟨123095690341143296797517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 328255174243048791460045 123095690341143296797517)
                      ·
                        rfl

theorem cell23_239728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 3].length) (baseStart_239728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239728 prefixEnd_239728 := by exact prefixLift 239728
  have htrace : WordTrace (prefixWord ++ tailWord_239728) baseStart_239728 baseEnd_239728 := by
    simpa [prefixWord, tailWord_239728, baseEnd_239728] using wordTrace_append hprefix tailTrace_239728
  have hstable : (prefixWord ++ tailWord_239728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239728).length < 2 ^ (prefixWord ++ tailWord_239728).sum := by decide
  have hdescent : baseEnd_239728 < baseStart_239728 := by decide
  rcases family_descends (prefixWord ++ tailWord_239728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239745 : List Nat := [1, 2, 4, 2, 3, 2, 1, 1, 1, 1, 5]
def baseStart_239745 : Nat := 118140960795 + 239745 * 2 ^ 59
def prefixEnd_239745 : Nat := 4983230072969 + 3 ^ 40 * 239745 * 2
def baseEnd_239745 : Nat := 123104419512269730284939

theorem tailTrace_239745 : CollatzResearch.WordTrace tailWord_239745 prefixEnd_239745 123104419512269730284939 := by
  unfold tailWord_239745
  simp only [CollatzResearch.WordTrace]
  refine ⟨8744218516452285031296689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5829479010968190020864459 8744218516452285031296689)
  ·
    refine ⟨6558163887339213773472517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8744218516452285031296689 6558163887339213773472517)
    ·
      refine ⟨1229655728876102582526097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6558163887339213773472517 1229655728876102582526097)
      ·
        refine ⟨922241796657076936894573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1229655728876102582526097 922241796657076936894573)
        ·
          refine ⟨345840673746403851335465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 922241796657076936894573 345840673746403851335465)
          ·
            refine ⟨259380505309802888501599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345840673746403851335465 259380505309802888501599)
            ·
              refine ⟨389070757964704332752399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259380505309802888501599 389070757964704332752399)
              ·
                refine ⟨583606136947056499128599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 389070757964704332752399 583606136947056499128599)
                ·
                  refine ⟨875409205420584748692899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 583606136947056499128599 875409205420584748692899)
                  ·
                    refine ⟨1313113808130877123039349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 875409205420584748692899 1313113808130877123039349)
                    ·
                      refine ⟨123104419512269730284939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1313113808130877123039349 123104419512269730284939)
                      ·
                        rfl

theorem cell23_239745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_239745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239745 prefixEnd_239745 := by exact prefixLift 239745
  have htrace : WordTrace (prefixWord ++ tailWord_239745) baseStart_239745 baseEnd_239745 := by
    simpa [prefixWord, tailWord_239745, baseEnd_239745] using wordTrace_append hprefix tailTrace_239745
  have hstable : (prefixWord ++ tailWord_239745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239745).length < 2 ^ (prefixWord ++ tailWord_239745).sum := by decide
  have hdescent : baseEnd_239745 < baseStart_239745 := by decide
  rcases family_descends (prefixWord ++ tailWord_239745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239775 : List Nat := [1, 1, 2, 6, 1, 2, 2, 1, 1, 3, 3]
def baseStart_239775 : Nat := 118140960795 + 239775 * 2 ^ 59
def prefixEnd_239775 : Nat := 4983230072969 + 3 ^ 40 * 239775 * 2
def baseEnd_239775 : Nat := 123119823931904612909801

theorem tailTrace_239775 : CollatzResearch.WordTrace tailWord_239775 prefixEnd_239775 123119823931904612909801 := by
  unfold tailWord_239775
  simp only [CollatzResearch.WordTrace]
  refine ⟨8745312706343600154888779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5830208470895733436592519 8745312706343600154888779)
  ·
    refine ⟨13117969059515400232333169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8745312706343600154888779 13117969059515400232333169)
    ·
      refine ⟨9838476794636550174249877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13117969059515400232333169 9838476794636550174249877)
      ·
        refine ⟨461178599748588289417963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9838476794636550174249877 461178599748588289417963)
        ·
          refine ⟨691767899622882434126945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461178599748588289417963 691767899622882434126945)
          ·
            refine ⟨518825924717161825595209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 691767899622882434126945 518825924717161825595209)
            ·
              refine ⟨389119443537871369196407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 518825924717161825595209 389119443537871369196407)
              ·
                refine ⟨583679165306807053794611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 389119443537871369196407 583679165306807053794611)
                ·
                  refine ⟨875518747960210580691917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 583679165306807053794611 875518747960210580691917)
                  ·
                    refine ⟨328319530485078967759469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 875518747960210580691917 328319530485078967759469)
                    ·
                      refine ⟨123119823931904612909801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 328319530485078967759469 123119823931904612909801)
                      ·
                        rfl

theorem cell23_239775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_239775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239775 prefixEnd_239775 := by exact prefixLift 239775
  have htrace : WordTrace (prefixWord ++ tailWord_239775) baseStart_239775 baseEnd_239775 := by
    simpa [prefixWord, tailWord_239775, baseEnd_239775] using wordTrace_append hprefix tailTrace_239775
  have hstable : (prefixWord ++ tailWord_239775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239775).length < 2 ^ (prefixWord ++ tailWord_239775).sum := by decide
  have hdescent : baseEnd_239775 < baseStart_239775 := by decide
  rcases family_descends (prefixWord ++ tailWord_239775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239781 : List Nat := [1, 3, 1, 2, 1, 3, 1, 2, 2, 3, 4]
def baseStart_239781 : Nat := 118140960795 + 239781 * 2 ^ 59
def prefixEnd_239781 : Nat := 4983230072969 + 3 ^ 40 * 239781 * 2
def baseEnd_239781 : Nat := 123122904815831589434773

theorem tailTrace_239781 : CollatzResearch.WordTrace tailWord_239781 prefixEnd_239781 123122904815831589434773 := by
  unfold tailWord_239781
  simp only [CollatzResearch.WordTrace]
  refine ⟨8745531544321863179607197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5830354362881242119738131 8745531544321863179607197)
  ·
    refine ⟨3279574329120698692352699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8745531544321863179607197 3279574329120698692352699)
    ·
      refine ⟨4919361493681048038529049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3279574329120698692352699 4919361493681048038529049)
      ·
        refine ⟨3689521120260786028896787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4919361493681048038529049 3689521120260786028896787)
        ·
          refine ⟨5534281680391179043345181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3689521120260786028896787 5534281680391179043345181)
          ·
            refine ⟨2075355630146692141254443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5534281680391179043345181 2075355630146692141254443)
            ·
              refine ⟨3113033445220038211881665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2075355630146692141254443 3113033445220038211881665)
              ·
                refine ⟨2334775083915028658911249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3113033445220038211881665 2334775083915028658911249)
                ·
                  refine ⟨1751081312936271494183437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2334775083915028658911249 1751081312936271494183437)
                  ·
                    refine ⟨656655492351101810318789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1751081312936271494183437 656655492351101810318789)
                    ·
                      refine ⟨123122904815831589434773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 656655492351101810318789 123122904815831589434773)
                      ·
                        rfl

theorem cell23_239781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_239781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239781 prefixEnd_239781 := by exact prefixLift 239781
  have htrace : WordTrace (prefixWord ++ tailWord_239781) baseStart_239781 baseEnd_239781 := by
    simpa [prefixWord, tailWord_239781, baseEnd_239781] using wordTrace_append hprefix tailTrace_239781
  have hstable : (prefixWord ++ tailWord_239781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239781).length < 2 ^ (prefixWord ++ tailWord_239781).sum := by decide
  have hdescent : baseEnd_239781 < baseStart_239781 := by decide
  rcases family_descends (prefixWord ++ tailWord_239781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239796 : List Nat := [2, 5, 3, 1, 1, 1, 1, 3, 1, 2, 3]
def baseStart_239796 : Nat := 118140960795 + 239796 * 2 ^ 59
def prefixEnd_239796 : Nat := 4983230072969 + 3 ^ 40 * 239796 * 2
def baseEnd_239796 : Nat := 123130607025649030747205

theorem tailTrace_239796 : CollatzResearch.WordTrace tailWord_239796 prefixEnd_239796 123130607025649030747205 := by
  unfold tailWord_239796
  simp only [CollatzResearch.WordTrace]
  refine ⟨4373039319633760370701621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5830719092845013827602161 4373039319633760370701621)
  ·
    refine ⟨409972436215665034753277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4373039319633760370701621 409972436215665034753277)
    ·
      refine ⟨153739663580874388032479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 409972436215665034753277 153739663580874388032479)
      ·
        refine ⟨230609495371311582048719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153739663580874388032479 230609495371311582048719)
        ·
          refine ⟨345914243056967373073079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230609495371311582048719 345914243056967373073079)
          ·
            refine ⟨518871364585451059609619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345914243056967373073079 518871364585451059609619)
            ·
              refine ⟨778307046878176589414429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518871364585451059609619 778307046878176589414429)
              ·
                refine ⟨291865142579316221030411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 778307046878176589414429 291865142579316221030411)
                ·
                  refine ⟨437797713868974331545617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 291865142579316221030411 437797713868974331545617)
                  ·
                    refine ⟨328348285401730748659213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 437797713868974331545617 328348285401730748659213)
                    ·
                      refine ⟨123130607025649030747205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 328348285401730748659213 123130607025649030747205)
                      ·
                        rfl

theorem cell23_239796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_239796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239796 prefixEnd_239796 := by exact prefixLift 239796
  have htrace : WordTrace (prefixWord ++ tailWord_239796) baseStart_239796 baseEnd_239796 := by
    simpa [prefixWord, tailWord_239796, baseEnd_239796] using wordTrace_append hprefix tailTrace_239796
  have hstable : (prefixWord ++ tailWord_239796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239796).length < 2 ^ (prefixWord ++ tailWord_239796).sum := by decide
  have hdescent : baseEnd_239796 < baseStart_239796 := by decide
  rcases family_descends (prefixWord ++ tailWord_239796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239801 : List Nat := [1, 2, 1, 4, 1, 2, 2, 1, 1, 3, 5]
def baseStart_239801 : Nat := 118140960795 + 239801 * 2 ^ 59
def prefixEnd_239801 : Nat := 4983230072969 + 3 ^ 40 * 239801 * 2
def baseEnd_239801 : Nat := 123133174428921511184681

theorem tailTrace_239801 : CollatzResearch.WordTrace tailWord_239801 prefixEnd_239801 123133174428921511184681 := by
  unfold tailWord_239801
  simp only [CollatzResearch.WordTrace]
  refine ⟨8746261004249406595335257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5830840669499604396890171 8746261004249406595335257)
  ·
    refine ⟨6559695753187054946501443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8746261004249406595335257 6559695753187054946501443)
    ·
      refine ⟨9839543629780582419752165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6559695753187054946501443 9839543629780582419752165)
      ·
        refine ⟨1844914430583859203703531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9839543629780582419752165 1844914430583859203703531)
        ·
          refine ⟨2767371645875788805555297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1844914430583859203703531 2767371645875788805555297)
          ·
            refine ⟨2075528734406841604166473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2767371645875788805555297 2075528734406841604166473)
            ·
              refine ⟨1556646550805131203124855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2075528734406841604166473 1556646550805131203124855)
              ·
                refine ⟨2334969826207696804687283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1556646550805131203124855 2334969826207696804687283)
                ·
                  refine ⟨3502454739311545207030925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2334969826207696804687283 3502454739311545207030925)
                  ·
                    refine ⟨1313420527241829452636597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3502454739311545207030925 1313420527241829452636597)
                    ·
                      refine ⟨123133174428921511184681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1313420527241829452636597 123133174428921511184681)
                      ·
                        rfl

theorem cell23_239801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_239801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239801 prefixEnd_239801 := by exact prefixLift 239801
  have htrace : WordTrace (prefixWord ++ tailWord_239801) baseStart_239801 baseEnd_239801 := by
    simpa [prefixWord, tailWord_239801, baseEnd_239801] using wordTrace_append hprefix tailTrace_239801
  have hstable : (prefixWord ++ tailWord_239801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239801).length < 2 ^ (prefixWord ++ tailWord_239801).sum := by decide
  have hdescent : baseEnd_239801 < baseStart_239801 := by decide
  rcases family_descends (prefixWord ++ tailWord_239801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239802 : List Nat := [3, 1, 1, 1, 2, 2, 6, 1, 1, 3, 2]
def baseStart_239802 : Nat := 118140960795 + 239802 * 2 ^ 59
def prefixEnd_239802 : Nat := 4983230072969 + 3 ^ 40 * 239802 * 2
def baseEnd_239802 : Nat := 123133687909576007272177

theorem tailTrace_239802 : CollatzResearch.WordTrace tailWord_239802 prefixEnd_239802 123133687909576007272177 := by
  unfold tailWord_239802
  simp only [CollatzResearch.WordTrace]
  refine ⟨2186574369311445941530415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5830864984830522510747773 2186574369311445941530415)
  ·
    refine ⟨3279861553967168912295623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2186574369311445941530415 3279861553967168912295623)
    ·
      refine ⟨4919792330950753368443435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3279861553967168912295623 4919792330950753368443435)
      ·
        refine ⟨7379688496426130052665153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4919792330950753368443435 7379688496426130052665153)
        ·
          refine ⟨5534766372319597539498865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7379688496426130052665153 5534766372319597539498865)
          ·
            refine ⟨4151074779239698154624149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5534766372319597539498865 4151074779239698154624149)
            ·
              refine ⟨194581630276860850998007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4151074779239698154624149 194581630276860850998007)
              ·
                refine ⟨291872445415291276497011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194581630276860850998007 291872445415291276497011)
                ·
                  refine ⟨437808668122936914745517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 291872445415291276497011 437808668122936914745517)
                  ·
                    refine ⟨164178250546101343029569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 437808668122936914745517 164178250546101343029569)
                    ·
                      refine ⟨123133687909576007272177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 164178250546101343029569 123133687909576007272177)
                      ·
                        rfl

theorem cell23_239802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 1, 1, 3, 2].length) (baseStart_239802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239802 prefixEnd_239802 := by exact prefixLift 239802
  have htrace : WordTrace (prefixWord ++ tailWord_239802) baseStart_239802 baseEnd_239802 := by
    simpa [prefixWord, tailWord_239802, baseEnd_239802] using wordTrace_append hprefix tailTrace_239802
  have hstable : (prefixWord ++ tailWord_239802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239802).length < 2 ^ (prefixWord ++ tailWord_239802).sum := by decide
  have hdescent : baseEnd_239802 < baseStart_239802 := by decide
  rcases family_descends (prefixWord ++ tailWord_239802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239832 : List Nat := [2, 1, 2, 2, 4, 3, 1, 1, 1, 4, 2]
def baseStart_239832 : Nat := 118140960795 + 239832 * 2 ^ 59
def prefixEnd_239832 : Nat := 4983230072969 + 3 ^ 40 * 239832 * 2
def baseEnd_239832 : Nat := 123149092329210889897039

theorem tailTrace_239832 : CollatzResearch.WordTrace tailWord_239832 prefixEnd_239832 123149092329210889897039 := by
  unfold tailWord_239832
  simp only [CollatzResearch.WordTrace]
  refine ⟨4373695833568549444856875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5831594444758065926475833 4373695833568549444856875)
  ·
    refine ⟨6560543750352824167285313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4373695833568549444856875 6560543750352824167285313)
    ·
      refine ⟨4920407812764618125463985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6560543750352824167285313 4920407812764618125463985)
      ·
        refine ⟨3690305859573463594097989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4920407812764618125463985 3690305859573463594097989)
        ·
          refine ⟨691932348670024423893373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3690305859573463594097989 691932348670024423893373)
          ·
            refine ⟨259474630751259158960015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 691932348670024423893373 259474630751259158960015)
            ·
              refine ⟨389211946126888738440023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259474630751259158960015 389211946126888738440023)
              ·
                refine ⟨583817919190333107660035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 389211946126888738440023 583817919190333107660035)
                ·
                  refine ⟨875726878785499661490053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 583817919190333107660035 875726878785499661490053)
                  ·
                    refine ⟨164198789772281186529385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 875726878785499661490053 164198789772281186529385)
                    ·
                      refine ⟨123149092329210889897039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 164198789772281186529385 123149092329210889897039)
                      ·
                        rfl

theorem cell23_239832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 1, 4, 2].length) (baseStart_239832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239832 prefixEnd_239832 := by exact prefixLift 239832
  have htrace : WordTrace (prefixWord ++ tailWord_239832) baseStart_239832 baseEnd_239832 := by
    simpa [prefixWord, tailWord_239832, baseEnd_239832] using wordTrace_append hprefix tailTrace_239832
  have hstable : (prefixWord ++ tailWord_239832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239832).length < 2 ^ (prefixWord ++ tailWord_239832).sum := by decide
  have hdescent : baseEnd_239832 < baseStart_239832 := by decide
  rcases family_descends (prefixWord ++ tailWord_239832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239836 : List Nat := [2, 2, 5, 2, 1, 1, 2, 2, 1, 3, 2]
def baseStart_239836 : Nat := 118140960795 + 239836 * 2 ^ 59
def prefixEnd_239836 : Nat := 4983230072969 + 3 ^ 40 * 239836 * 2
def baseEnd_239836 : Nat := 123151146251828874247021

theorem tailTrace_239836 : CollatzResearch.WordTrace tailWord_239836 prefixEnd_239836 123151146251828874247021 := by
  unfold tailWord_239836
  simp only [CollatzResearch.WordTrace]
  refine ⟨4373768779561303786429681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5831691706081738381906241 4373768779561303786429681)
  ·
    refine ⟨3280326584670977839822261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4373768779561303786429681 3280326584670977839822261)
    ·
      refine ⟨307530617312904172483337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3280326584670977839822261 307530617312904172483337)
      ·
        refine ⟨230647962984678129362503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307530617312904172483337 230647962984678129362503)
        ·
          refine ⟨345971944477017194043755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230647962984678129362503 345971944477017194043755)
          ·
            refine ⟨518957916715525791065633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345971944477017194043755 518957916715525791065633)
            ·
              refine ⟨389218437536644343299225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 518957916715525791065633 389218437536644343299225)
              ·
                refine ⟨291913828152483257474419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 389218437536644343299225 291913828152483257474419)
                ·
                  refine ⟨437870742228724886211629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 291913828152483257474419 437870742228724886211629)
                  ·
                    refine ⟨164201528335771832329361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 437870742228724886211629 164201528335771832329361)
                    ·
                      refine ⟨123151146251828874247021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 164201528335771832329361 123151146251828874247021)
                      ·
                        rfl

theorem cell23_239836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_239836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239836 prefixEnd_239836 := by exact prefixLift 239836
  have htrace : WordTrace (prefixWord ++ tailWord_239836) baseStart_239836 baseEnd_239836 := by
    simpa [prefixWord, tailWord_239836, baseEnd_239836] using wordTrace_append hprefix tailTrace_239836
  have hstable : (prefixWord ++ tailWord_239836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239836).length < 2 ^ (prefixWord ++ tailWord_239836).sum := by decide
  have hdescent : baseEnd_239836 < baseStart_239836 := by decide
  rcases family_descends (prefixWord ++ tailWord_239836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239851 : List Nat := [1, 1, 1, 1, 2, 5, 1, 3, 1, 7]
def baseStart_239851 : Nat := 118140960795 + 239851 * 2 ^ 59
def prefixEnd_239851 : Nat := 4983230072969 + 3 ^ 40 * 239851 * 2
def baseEnd_239851 : Nat := 41052949487215438519817

theorem tailTrace_239851 : CollatzResearch.WordTrace tailWord_239851 prefixEnd_239851 41052949487215438519817 := by
  unfold tailWord_239851
  simp only [CollatzResearch.WordTrace]
  refine ⟨8748084654068265134655407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5832056436045510089770271 8748084654068265134655407)
  ·
    refine ⟨13122126981102397701983111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8748084654068265134655407 13122126981102397701983111)
    ·
      refine ⟨19683190471653596552974667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13122126981102397701983111 19683190471653596552974667)
      ·
        refine ⟨29524785707480394829462001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19683190471653596552974667 29524785707480394829462001)
        ·
          refine ⟨22143589280610296122096501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29524785707480394829462001 22143589280610296122096501)
          ·
            refine ⟨2075961495057215261446547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22143589280610296122096501 2075961495057215261446547)
            ·
              refine ⟨3113942242585822892169821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2075961495057215261446547 3113942242585822892169821)
              ·
                refine ⟨1167728340969683584563683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3113942242585822892169821 1167728340969683584563683)
                ·
                  refine ⟨1751592511454525376845525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1167728340969683584563683 1751592511454525376845525)
                  ·
                    refine ⟨41052949487215438519817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1751592511454525376845525 41052949487215438519817)
                    ·
                      rfl

theorem cell23_239851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 7].length) (baseStart_239851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239851 prefixEnd_239851 := by exact prefixLift 239851
  have htrace : WordTrace (prefixWord ++ tailWord_239851) baseStart_239851 baseEnd_239851 := by
    simpa [prefixWord, tailWord_239851, baseEnd_239851] using wordTrace_append hprefix tailTrace_239851
  have hstable : (prefixWord ++ tailWord_239851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239851).length < 2 ^ (prefixWord ++ tailWord_239851).sum := by decide
  have hdescent : baseEnd_239851 < baseStart_239851 := by decide
  rcases family_descends (prefixWord ++ tailWord_239851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239855 : List Nat := [1, 1, 2, 1, 6, 1, 3, 3, 5]
def baseStart_239855 : Nat := 118140960795 + 239855 * 2 ^ 59
def prefixEnd_239855 : Nat := 4983230072969 + 3 ^ 40 * 239855 * 2
def baseEnd_239855 : Nat := 13684544709362699989937

theorem tailTrace_239855 : CollatzResearch.WordTrace tailWord_239855 prefixEnd_239855 13684544709362699989937 := by
  unfold tailWord_239855
  simp only [CollatzResearch.WordTrace]
  refine ⟨8748230546053773817801019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5832153697369182545200679 8748230546053773817801019)
  ·
    refine ⟨13122345819080660726701529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8748230546053773817801019 13122345819080660726701529)
    ·
      refine ⟨9841759364310495545026147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13122345819080660726701529 9841759364310495545026147)
      ·
        refine ⟨14762639046465743317539221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9841759364310495545026147 14762639046465743317539221)
        ·
          refine ⟨691998705303081718009651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14762639046465743317539221 691998705303081718009651)
          ·
            refine ⟨1037998057954622577014477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 691998705303081718009651 1037998057954622577014477)
            ·
              refine ⟨389249271732983466380429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1037998057954622577014477 389249271732983466380429)
              ·
                refine ⟨145968476899868799892661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 389249271732983466380429 145968476899868799892661)
                ·
                  refine ⟨13684544709362699989937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 145968476899868799892661 13684544709362699989937)
                  ·
                    rfl

theorem cell23_239855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 3, 5].length) (baseStart_239855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239855 prefixEnd_239855 := by exact prefixLift 239855
  have htrace : WordTrace (prefixWord ++ tailWord_239855) baseStart_239855 baseEnd_239855 := by
    simpa [prefixWord, tailWord_239855, baseEnd_239855] using wordTrace_append hprefix tailTrace_239855
  have hstable : (prefixWord ++ tailWord_239855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239855).length < 2 ^ (prefixWord ++ tailWord_239855).sum := by decide
  have hdescent : baseEnd_239855 < baseStart_239855 := by decide
  rcases family_descends (prefixWord ++ tailWord_239855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239868 : List Nat := [2, 2, 2, 1, 4, 1, 1, 1, 4, 5]
def baseStart_239868 : Nat := 118140960795 + 239868 * 2 ^ 59
def prefixEnd_239868 : Nat := 4983230072969 + 3 ^ 40 * 239868 * 2
def baseEnd_239868 : Nat := 41055859210924249682291

theorem tailTrace_239868 : CollatzResearch.WordTrace tailWord_239868 prefixEnd_239868 41055859210924249682291 := by
  unfold tailWord_239868
  simp only [CollatzResearch.WordTrace]
  refine ⟨4374352347503338519012129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5832469796671118025349505 4374352347503338519012129)
  ·
    refine ⟨3280764260627503889259097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4374352347503338519012129 3280764260627503889259097)
    ·
      refine ⟨2460573195470627916944323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3280764260627503889259097 2460573195470627916944323)
      ·
        refine ⟨3690859793205941875416485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2460573195470627916944323 3690859793205941875416485)
        ·
          refine ⟨692036211226114101640591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3690859793205941875416485 692036211226114101640591)
          ·
            refine ⟨1038054316839171152460887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 692036211226114101640591 1038054316839171152460887)
            ·
              refine ⟨1557081475258756728691331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1038054316839171152460887 1557081475258756728691331)
              ·
                refine ⟨2335622212888135093036997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1557081475258756728691331 2335622212888135093036997)
                ·
                  refine ⟨437929164916525329944437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2335622212888135093036997 437929164916525329944437)
                  ·
                    refine ⟨41055859210924249682291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 437929164916525329944437 41055859210924249682291)
                    ·
                      rfl

theorem cell23_239868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_239868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239868 prefixEnd_239868 := by exact prefixLift 239868
  have htrace : WordTrace (prefixWord ++ tailWord_239868) baseStart_239868 baseEnd_239868 := by
    simpa [prefixWord, tailWord_239868, baseEnd_239868] using wordTrace_append hprefix tailTrace_239868
  have hstable : (prefixWord ++ tailWord_239868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239868).length < 2 ^ (prefixWord ++ tailWord_239868).sum := by decide
  have hdescent : baseEnd_239868 < baseStart_239868 := by decide
  rcases family_descends (prefixWord ++ tailWord_239868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239891 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 5]
def baseStart_239891 : Nat := 118140960795 + 239891 * 2 ^ 59
def prefixEnd_239891 : Nat := 4983230072969 + 3 ^ 40 * 239891 * 2
def baseEnd_239891 : Nat := 123179387687826159059267

theorem tailTrace_239891 : CollatzResearch.WordTrace tailWord_239891 prefixEnd_239891 123179387687826159059267 := by
  unfold tailWord_239891
  simp only [CollatzResearch.WordTrace]
  refine ⟨8749543573923351966111527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5833029049282234644074351 8749543573923351966111527)
  ·
    refine ⟨13124315360885027949167291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8749543573923351966111527 13124315360885027949167291)
    ·
      refine ⟨19686473041327541923750937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13124315360885027949167291 19686473041327541923750937)
      ·
        refine ⟨14764854780995656442813203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19686473041327541923750937 14764854780995656442813203)
        ·
          refine ⟨22147282171493484664219805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14764854780995656442813203 22147282171493484664219805)
          ·
            refine ⟨8305230814310056749082427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22147282171493484664219805 8305230814310056749082427)
            ·
              refine ⟨12457846221465085123623641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8305230814310056749082427 12457846221465085123623641)
              ·
                refine ⟨9343384666098813842717731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12457846221465085123623641 9343384666098813842717731)
                ·
                  refine ⟨14015076999148220764076597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9343384666098813842717731 14015076999148220764076597)
                  ·
                    refine ⟨1313913468670145696632181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14015076999148220764076597 1313913468670145696632181)
                    ·
                      refine ⟨123179387687826159059267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1313913468670145696632181 123179387687826159059267)
                      ·
                        rfl

theorem cell23_239891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 5].length) (baseStart_239891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239891 prefixEnd_239891 := by exact prefixLift 239891
  have htrace : WordTrace (prefixWord ++ tailWord_239891) baseStart_239891 baseEnd_239891 := by
    simpa [prefixWord, tailWord_239891, baseEnd_239891] using wordTrace_append hprefix tailTrace_239891
  have hstable : (prefixWord ++ tailWord_239891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239891).length < 2 ^ (prefixWord ++ tailWord_239891).sum := by decide
  have hdescent : baseEnd_239891 < baseStart_239891 := by decide
  rcases family_descends (prefixWord ++ tailWord_239891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239902 : List Nat := [4, 3, 2, 1, 1, 1, 1, 3, 2, 5]
def baseStart_239902 : Nat := 118140960795 + 239902 * 2 ^ 59
def prefixEnd_239902 : Nat := 4983230072969 + 3 ^ 40 * 239902 * 2
def baseEnd_239902 : Nat := 41061678658341872007239

theorem tailTrace_239902 : CollatzResearch.WordTrace tailWord_239902 prefixEnd_239902 41061678658341872007239 := by
  unfold tailWord_239902
  simp only [CollatzResearch.WordTrace]
  refine ⟨1093743097110437605595245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5833296517922333896507973 1093743097110437605595245)
  ·
    refine ⟨410153661416414102098217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1093743097110437605595245 410153661416414102098217)
    ·
      refine ⟨307615246062310576573663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410153661416414102098217 307615246062310576573663)
      ·
        refine ⟨461422869093465864860495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307615246062310576573663 461422869093465864860495)
        ·
          refine ⟨692134303640198797290743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461422869093465864860495 692134303640198797290743)
          ·
            refine ⟨1038201455460298195936115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 692134303640198797290743 1038201455460298195936115)
            ·
              refine ⟨1557302183190447293904173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1038201455460298195936115 1557302183190447293904173)
              ·
                refine ⟨583988318696417735214065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1557302183190447293904173 583988318696417735214065)
                ·
                  refine ⟨437991239022313301410549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 583988318696417735214065 437991239022313301410549)
                  ·
                    refine ⟨41061678658341872007239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 437991239022313301410549 41061678658341872007239)
                    ·
                      rfl

theorem cell23_239902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_239902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239902 prefixEnd_239902 := by exact prefixLift 239902
  have htrace : WordTrace (prefixWord ++ tailWord_239902) baseStart_239902 baseEnd_239902 := by
    simpa [prefixWord, tailWord_239902, baseEnd_239902] using wordTrace_append hprefix tailTrace_239902
  have hstable : (prefixWord ++ tailWord_239902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239902).length < 2 ^ (prefixWord ++ tailWord_239902).sum := by decide
  have hdescent : baseEnd_239902 < baseStart_239902 := by decide
  rcases family_descends (prefixWord ++ tailWord_239902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239925 : List Nat := [1, 3, 3, 1, 2, 1, 1, 4, 2, 2, 3]
def baseStart_239925 : Nat := 118140960795 + 239925 * 2 ^ 59
def prefixEnd_239925 : Nat := 4983230072969 + 3 ^ 40 * 239925 * 2
def baseEnd_239925 : Nat := 123196846030079026034111

theorem tailTrace_239925 : CollatzResearch.WordTrace tailWord_239925 prefixEnd_239925 123196846030079026034111 := by
  unfold tailWord_239925
  simp only [CollatzResearch.WordTrace]
  refine ⟨8750783655800175772849229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5833855770533450515232819 8750783655800175772849229)
  ·
    refine ⟨3281543870925065914818461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8750783655800175772849229 3281543870925065914818461)
    ·
      refine ⟨1230578951596899718056923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3281543870925065914818461 1230578951596899718056923)
      ·
        refine ⟨1845868427395349577085385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1230578951596899718056923 1845868427395349577085385)
        ·
          refine ⟨1384401320546512182814039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1845868427395349577085385 1384401320546512182814039)
          ·
            refine ⟨2076601980819768274221059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1384401320546512182814039 2076601980819768274221059)
            ·
              refine ⟨3114902971229652411331589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2076601980819768274221059 3114902971229652411331589)
              ·
                refine ⟨584044307105559827124673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3114902971229652411331589 584044307105559827124673)
                ·
                  refine ⟨438033230329169870343505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 584044307105559827124673 438033230329169870343505)
                  ·
                    refine ⟨328524922746877402757629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 438033230329169870343505 328524922746877402757629)
                    ·
                      refine ⟨123196846030079026034111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 328524922746877402757629 123196846030079026034111)
                      ·
                        rfl

theorem cell23_239925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_239925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239925 prefixEnd_239925 := by exact prefixLift 239925
  have htrace : WordTrace (prefixWord ++ tailWord_239925) baseStart_239925 baseEnd_239925 := by
    simpa [prefixWord, tailWord_239925, baseEnd_239925] using wordTrace_append hprefix tailTrace_239925
  have hstable : (prefixWord ++ tailWord_239925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239925).length < 2 ^ (prefixWord ++ tailWord_239925).sum := by decide
  have hdescent : baseEnd_239925 < baseStart_239925 := by decide
  rcases family_descends (prefixWord ++ tailWord_239925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239928 : List Nat := [2, 1, 2, 1, 3, 1, 3, 4, 6]
def baseStart_239928 : Nat := 118140960795 + 239928 * 2 ^ 59
def prefixEnd_239928 : Nat := 4983230072969 + 3 ^ 40 * 239928 * 2
def baseEnd_239928 : Nat := 13688709608004723810733

theorem tailTrace_239928 : CollatzResearch.WordTrace tailWord_239928 prefixEnd_239928 13688709608004723810733 := by
  unfold tailWord_239928
  simp only [CollatzResearch.WordTrace]
  refine ⟨4375446537394653642604219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5833928716526204856805625 4375446537394653642604219)
  ·
    refine ⟨6563169806091980463906329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4375446537394653642604219 6563169806091980463906329)
    ·
      refine ⟨4922377354568985347929747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6563169806091980463906329 4922377354568985347929747)
      ·
        refine ⟨7383566031853478021894621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4922377354568985347929747 7383566031853478021894621)
        ·
          refine ⟨2768837261945054258210483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7383566031853478021894621 2768837261945054258210483)
          ·
            refine ⟨4153255892917581387315725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2768837261945054258210483 4153255892917581387315725)
            ·
              refine ⟨1557470959844093020243397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4153255892917581387315725 1557470959844093020243397)
              ·
                refine ⟨292025804970767441295637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1557470959844093020243397 292025804970767441295637)
                ·
                  refine ⟨13688709608004723810733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 292025804970767441295637 13688709608004723810733)
                  ·
                    rfl

theorem cell23_239928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4, 6].length) (baseStart_239928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239928 prefixEnd_239928 := by exact prefixLift 239928
  have htrace : WordTrace (prefixWord ++ tailWord_239928) baseStart_239928 baseEnd_239928 := by
    simpa [prefixWord, tailWord_239928, baseEnd_239928] using wordTrace_append hprefix tailTrace_239928
  have hstable : (prefixWord ++ tailWord_239928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239928).length < 2 ^ (prefixWord ++ tailWord_239928).sum := by decide
  have hdescent : baseEnd_239928 < baseStart_239928 := by decide
  rcases family_descends (prefixWord ++ tailWord_239928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239932 : List Nat := [2, 2, 2, 2, 1, 2, 3, 4, 1, 4]
def baseStart_239932 : Nat := 118140960795 + 239932 * 2 ^ 59
def prefixEnd_239932 : Nat := 4983230072969 + 3 ^ 40 * 239932 * 2
def baseEnd_239932 : Nat := 41066813464886832882193

theorem tailTrace_239932 : CollatzResearch.WordTrace tailWord_239932 prefixEnd_239932 41066813464886832882193 := by
  unfold tailWord_239932
  simp only [CollatzResearch.WordTrace]
  refine ⟨4375519483387407984177025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5834025977849877312236033 4375519483387407984177025)
  ·
    refine ⟨3281639612540555988132769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4375519483387407984177025 3281639612540555988132769)
    ·
      refine ⟨2461229709405416991099577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3281639612540555988132769 2461229709405416991099577)
      ·
        refine ⟨1845922282054062743324683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2461229709405416991099577 1845922282054062743324683)
        ·
          refine ⟨2768883423081094114987025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1845922282054062743324683 2768883423081094114987025)
          ·
            refine ⟨2076662567310820586240269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2768883423081094114987025 2076662567310820586240269)
            ·
              refine ⟨778748462741557719840101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2076662567310820586240269 778748462741557719840101)
              ·
                refine ⟨146015336764042072470019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 778748462741557719840101 146015336764042072470019)
                ·
                  refine ⟨219023005146063108705029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146015336764042072470019 219023005146063108705029)
                  ·
                    refine ⟨41066813464886832882193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 219023005146063108705029 41066813464886832882193)
                    ·
                      rfl

theorem cell23_239932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 4, 1, 4].length) (baseStart_239932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239932 prefixEnd_239932 := by exact prefixLift 239932
  have htrace : WordTrace (prefixWord ++ tailWord_239932) baseStart_239932 baseEnd_239932 := by
    simpa [prefixWord, tailWord_239932, baseEnd_239932] using wordTrace_append hprefix tailTrace_239932
  have hstable : (prefixWord ++ tailWord_239932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239932).length < 2 ^ (prefixWord ++ tailWord_239932).sum := by decide
  have hdescent : baseEnd_239932 < baseStart_239932 := by decide
  rcases family_descends (prefixWord ++ tailWord_239932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239989 : List Nat := [1, 3, 4, 1, 2, 2, 2, 1, 3, 1, 3]
def baseStart_239989 : Nat := 118140960795 + 239989 * 2 ^ 59
def prefixEnd_239989 : Nat := 4983230072969 + 3 ^ 40 * 239989 * 2
def baseEnd_239989 : Nat := 123229708791966775633817

theorem tailTrace_239989 : CollatzResearch.WordTrace tailWord_239989 prefixEnd_239989 123229708791966775633817 := by
  unfold tailWord_239989
  simp only [CollatzResearch.WordTrace]
  refine ⟨8753117927568314703179021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5835411951712209802119347 8753117927568314703179021)
  ·
    refine ⟨3282419222838118013692133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8753117927568314703179021 3282419222838118013692133)
    ·
      refine ⟨615453604282147127567275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3282419222838118013692133 615453604282147127567275)
      ·
        refine ⟨923180406423220691350913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 615453604282147127567275 923180406423220691350913)
        ·
          refine ⟨692385304817415518513185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 923180406423220691350913 692385304817415518513185)
          ·
            refine ⟨519288978613061638884889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 692385304817415518513185 519288978613061638884889)
            ·
              refine ⟨389466733959796229163667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 519288978613061638884889 389466733959796229163667)
              ·
                refine ⟨584200100939694343745501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 389466733959796229163667 584200100939694343745501)
                ·
                  refine ⟨219075037852385378904563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 584200100939694343745501 219075037852385378904563)
                  ·
                    refine ⟨328612556778578068356845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 219075037852385378904563 328612556778578068356845)
                    ·
                      refine ⟨123229708791966775633817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 328612556778578068356845 123229708791966775633817)
                      ·
                        rfl

theorem cell23_239989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_239989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_239989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_239989 prefixEnd_239989 := by exact prefixLift 239989
  have htrace : WordTrace (prefixWord ++ tailWord_239989) baseStart_239989 baseEnd_239989 := by
    simpa [prefixWord, tailWord_239989, baseEnd_239989] using wordTrace_append hprefix tailTrace_239989
  have hstable : (prefixWord ++ tailWord_239989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239989).length < 2 ^ (prefixWord ++ tailWord_239989).sum := by decide
  have hdescent : baseEnd_239989 < baseStart_239989 := by decide
  rcases family_descends (prefixWord ++ tailWord_239989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240012 : List Nat := [2, 2, 1, 2, 1, 5, 2, 2, 1, 1, 4]
def baseStart_240012 : Nat := 118140960795 + 240012 * 2 ^ 59
def prefixEnd_240012 : Nat := 4983230072969 + 3 ^ 40 * 240012 * 2
def baseEnd_240012 : Nat := 123241518847020185646211

theorem tailTrace_240012 : CollatzResearch.WordTrace tailWord_240012 prefixEnd_240012 123241518847020185646211 := by
  unfold tailWord_240012
  simp only [CollatzResearch.WordTrace]
  refine ⟨4376978403242494815633145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5835971204323326420844193 4376978403242494815633145)
  ·
    refine ⟨3282733802431871111724859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4376978403242494815633145 3282733802431871111724859)
    ·
      refine ⟨4924100703647806667587289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3282733802431871111724859 4924100703647806667587289)
      ·
        refine ⟨3693075527735855000690467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4924100703647806667587289 3693075527735855000690467)
        ·
          refine ⟨5539613291603782501035701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3693075527735855000690467 5539613291603782501035701)
          ·
            refine ⟨519338746087854609472097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5539613291603782501035701 519338746087854609472097)
            ·
              refine ⟨389504059565890957104073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 519338746087854609472097 389504059565890957104073)
              ·
                refine ⟨292128044674418217828055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 389504059565890957104073 292128044674418217828055)
                ·
                  refine ⟨438192067011627326742083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 292128044674418217828055 438192067011627326742083)
                  ·
                    refine ⟨657288100517440990113125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 438192067011627326742083 657288100517440990113125)
                    ·
                      refine ⟨123241518847020185646211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 657288100517440990113125 123241518847020185646211)
                      ·
                        rfl

theorem cell23_240012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2, 1, 1, 4].length) (baseStart_240012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240012 prefixEnd_240012 := by exact prefixLift 240012
  have htrace : WordTrace (prefixWord ++ tailWord_240012) baseStart_240012 baseEnd_240012 := by
    simpa [prefixWord, tailWord_240012, baseEnd_240012] using wordTrace_append hprefix tailTrace_240012
  have hstable : (prefixWord ++ tailWord_240012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240012).length < 2 ^ (prefixWord ++ tailWord_240012).sum := by decide
  have hdescent : baseEnd_240012 < baseStart_240012 := by decide
  rcases family_descends (prefixWord ++ tailWord_240012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240032 : List Nat := [2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 3]
def baseStart_240032 : Nat := 118140960795 + 240032 * 2 ^ 59
def prefixEnd_240032 : Nat := 4983230072969 + 3 ^ 40 * 240032 * 2
def baseEnd_240032 : Nat := 123251788460110107396119

theorem tailTrace_240032 : CollatzResearch.WordTrace tailWord_240032 prefixEnd_240032 123251788460110107396119 := by
  unfold tailWord_240032
  simp only [CollatzResearch.WordTrace]
  refine ⟨4377343133206266523497175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5836457510941688697996233 4377343133206266523497175)
  ·
    refine ⟨6566014699809399785245763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4377343133206266523497175 6566014699809399785245763)
    ·
      refine ⟨9849022049714099677868645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6566014699809399785245763 9849022049714099677868645)
      ·
        refine ⟨1846691634321393689600371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9849022049714099677868645 1846691634321393689600371)
        ·
          refine ⟨2770037451482090534400557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1846691634321393689600371 2770037451482090534400557)
          ·
            refine ⟨1038764044305783950400209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2770037451482090534400557 1038764044305783950400209)
            ·
              refine ⟨779073033229337962800157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1038764044305783950400209 779073033229337962800157)
              ·
                refine ⟨292152387461001736050059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 779073033229337962800157 292152387461001736050059)
                ·
                  refine ⟨438228581191502604075089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 292152387461001736050059 438228581191502604075089)
                  ·
                    refine ⟨328671435893626953056317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 438228581191502604075089 328671435893626953056317)
                    ·
                      refine ⟨123251788460110107396119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 328671435893626953056317 123251788460110107396119)
                      ·
                        rfl

theorem cell23_240032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_240032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240032 prefixEnd_240032 := by exact prefixLift 240032
  have htrace : WordTrace (prefixWord ++ tailWord_240032) baseStart_240032 baseEnd_240032 := by
    simpa [prefixWord, tailWord_240032, baseEnd_240032] using wordTrace_append hprefix tailTrace_240032
  have hstable : (prefixWord ++ tailWord_240032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240032).length < 2 ^ (prefixWord ++ tailWord_240032).sum := by decide
  have hdescent : baseEnd_240032 < baseStart_240032 := by decide
  rcases family_descends (prefixWord ++ tailWord_240032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240115 : List Nat := [1, 1, 1, 2, 2, 2, 5, 1, 2, 2, 4]
def baseStart_240115 : Nat := 118140960795 + 240115 * 2 ^ 59
def prefixEnd_240115 : Nat := 4983230072969 + 3 ^ 40 * 240115 * 2
def baseEnd_240115 : Nat := 123294407354433282658237

theorem tailTrace_240115 : CollatzResearch.WordTrace tailWord_240115 prefixEnd_240115 123294407354433282658237 := by
  unfold tailWord_240115
  simp only [CollatzResearch.WordTrace]
  refine ⟨8757713525111838222265799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5838475683407892148177199 8757713525111838222265799)
  ·
    refine ⟨13136570287667757333398699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8757713525111838222265799 13136570287667757333398699)
    ·
      refine ⟨19704855431501636000098049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13136570287667757333398699 19704855431501636000098049)
      ·
        refine ⟨14778641573626227000073537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19704855431501636000098049 14778641573626227000073537)
        ·
          refine ⟨11083981180219670250055153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14778641573626227000073537 11083981180219670250055153)
          ·
            refine ⟨8312985885164752687541365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11083981180219670250055153 8312985885164752687541365)
            ·
              refine ⟨779342426734195564457003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8312985885164752687541365 779342426734195564457003)
              ·
                refine ⟨1169013640101293346685505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 779342426734195564457003 1169013640101293346685505)
                ·
                  refine ⟨876760230075970010014129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1169013640101293346685505 876760230075970010014129)
                  ·
                    refine ⟨657570172556977507510597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 876760230075970010014129 657570172556977507510597)
                    ·
                      refine ⟨123294407354433282658237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 657570172556977507510597 123294407354433282658237)
                      ·
                        rfl

theorem cell23_240115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2, 4].length) (baseStart_240115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240115 prefixEnd_240115 := by exact prefixLift 240115
  have htrace : WordTrace (prefixWord ++ tailWord_240115) baseStart_240115 baseEnd_240115 := by
    simpa [prefixWord, tailWord_240115, baseEnd_240115] using wordTrace_append hprefix tailTrace_240115
  have hstable : (prefixWord ++ tailWord_240115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240115).length < 2 ^ (prefixWord ++ tailWord_240115).sum := by decide
  have hdescent : baseEnd_240115 < baseStart_240115 := by decide
  rcases family_descends (prefixWord ++ tailWord_240115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240125 : List Nat := [1, 4, 1, 1, 1, 3, 3, 2, 7]
def baseStart_240125 : Nat := 118140960795 + 240125 * 2 ^ 59
def prefixEnd_240125 : Nat := 4983230072969 + 3 ^ 40 * 240125 * 2
def baseEnd_240125 : Nat := 13699949128997582614799

theorem tailTrace_240125 : CollatzResearch.WordTrace tailWord_240125 prefixEnd_240125 13699949128997582614799 := by
  unfold tailWord_240125
  simp only [CollatzResearch.WordTrace]
  refine ⟨8758078255075609930129829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5838718836717073286753219 8758078255075609930129829)
  ·
    refine ⟨1642139672826676861899343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8758078255075609930129829 1642139672826676861899343)
    ·
      refine ⟨2463209509240015292849015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1642139672826676861899343 2463209509240015292849015)
      ·
        refine ⟨3694814263860022939273523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2463209509240015292849015 3694814263860022939273523)
        ·
          refine ⟨5542221395790034408910285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3694814263860022939273523 5542221395790034408910285)
          ·
            refine ⟨2078333023421262903341357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5542221395790034408910285 2078333023421262903341357)
            ·
              refine ⟨779374883782973588753009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2078333023421262903341357 779374883782973588753009)
              ·
                refine ⟨584531162837230191564757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 779374883782973588753009 584531162837230191564757)
                ·
                  refine ⟨13699949128997582614799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 584531162837230191564757 13699949128997582614799)
                  ·
                    rfl

theorem cell23_240125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 7].length) (baseStart_240125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240125 prefixEnd_240125 := by exact prefixLift 240125
  have htrace : WordTrace (prefixWord ++ tailWord_240125) baseStart_240125 baseEnd_240125 := by
    simpa [prefixWord, tailWord_240125, baseEnd_240125] using wordTrace_append hprefix tailTrace_240125
  have hstable : (prefixWord ++ tailWord_240125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240125).length < 2 ^ (prefixWord ++ tailWord_240125).sum := by decide
  have hdescent : baseEnd_240125 < baseStart_240125 := by decide
  rcases family_descends (prefixWord ++ tailWord_240125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240152 : List Nat := [2, 1, 2, 3, 3, 1, 1, 2, 2, 3, 3]
def baseStart_240152 : Nat := 118140960795 + 240152 * 2 ^ 59
def prefixEnd_240152 : Nat := 4983230072969 + 3 ^ 40 * 240152 * 2
def baseEnd_240152 : Nat := 123313406138649637895567

theorem tailTrace_240152 : CollatzResearch.WordTrace tailWord_240152 prefixEnd_240152 123313406138649637895567 := by
  unfold tailWord_240152
  simp only [CollatzResearch.WordTrace]
  refine ⟨4379531512988896770681355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5839375350651862360908473 4379531512988896770681355)
  ·
    refine ⟨6569297269483345156022033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4379531512988896770681355 6569297269483345156022033)
    ·
      refine ⟨4926972952112508867016525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6569297269483345156022033 4926972952112508867016525)
      ·
        refine ⟨1847614857042190825131197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4926972952112508867016525 1847614857042190825131197)
        ·
          refine ⟨692855571390821559424199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1847614857042190825131197 692855571390821559424199)
          ·
            refine ⟨1039283357086232339136299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 692855571390821559424199 1039283357086232339136299)
            ·
              refine ⟨1558925035629348508704449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1039283357086232339136299 1558925035629348508704449)
              ·
                refine ⟨1169193776722011381528337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1558925035629348508704449 1169193776722011381528337)
                ·
                  refine ⟨876895332541508536146253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1169193776722011381528337 876895332541508536146253)
                  ·
                    refine ⟨328835749703065701054845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 876895332541508536146253 328835749703065701054845)
                    ·
                      refine ⟨123313406138649637895567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 328835749703065701054845 123313406138649637895567)
                      ·
                        rfl

theorem cell23_240152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_240152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240152 prefixEnd_240152 := by exact prefixLift 240152
  have htrace : WordTrace (prefixWord ++ tailWord_240152) baseStart_240152 baseEnd_240152 := by
    simpa [prefixWord, tailWord_240152, baseEnd_240152] using wordTrace_append hprefix tailTrace_240152
  have hstable : (prefixWord ++ tailWord_240152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240152).length < 2 ^ (prefixWord ++ tailWord_240152).sum := by decide
  have hdescent : baseEnd_240152 < baseStart_240152 := by decide
  rcases family_descends (prefixWord ++ tailWord_240152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240165 : List Nat := [1, 3, 1, 2, 2, 1, 2, 3, 1, 2, 5]
def baseStart_240165 : Nat := 118140960795 + 240165 * 2 ^ 59
def prefixEnd_240165 : Nat := 4983230072969 + 3 ^ 40 * 240165 * 2
def baseEnd_240165 : Nat := 123320081387158087033007

theorem tailTrace_240165 : CollatzResearch.WordTrace tailWord_240165 prefixEnd_240165 123320081387158087033007 := by
  unfold tailWord_240165
  simp only [CollatzResearch.WordTrace]
  refine ⟨8759537174930696761585949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5839691449953797841057299 8759537174930696761585949)
  ·
    refine ⟨3284826440599011285594731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8759537174930696761585949 3284826440599011285594731)
    ·
      refine ⟨4927239660898516928392097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3284826440599011285594731 4927239660898516928392097)
      ·
        refine ⟨3695429745673887696294073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4927239660898516928392097 3695429745673887696294073)
        ·
          refine ⟨2771572309255415772220555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3695429745673887696294073 2771572309255415772220555)
          ·
            refine ⟨4157358463883123658330833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2771572309255415772220555 4157358463883123658330833)
            ·
              refine ⟨3118018847912342743748125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4157358463883123658330833 3118018847912342743748125)
              ·
                refine ⟨1169257067967128528905547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3118018847912342743748125 1169257067967128528905547)
                ·
                  refine ⟨1753885601950692793358321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1169257067967128528905547 1753885601950692793358321)
                  ·
                    refine ⟨1315414201463019595018741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1753885601950692793358321 1315414201463019595018741)
                    ·
                      refine ⟨123320081387158087033007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1315414201463019595018741 123320081387158087033007)
                      ·
                        rfl

theorem cell23_240165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_240165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240165 prefixEnd_240165 := by exact prefixLift 240165
  have htrace : WordTrace (prefixWord ++ tailWord_240165) baseStart_240165 baseEnd_240165 := by
    simpa [prefixWord, tailWord_240165, baseEnd_240165] using wordTrace_append hprefix tailTrace_240165
  have hstable : (prefixWord ++ tailWord_240165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240165).length < 2 ^ (prefixWord ++ tailWord_240165).sum := by decide
  have hdescent : baseEnd_240165 < baseStart_240165 := by decide
  rcases family_descends (prefixWord ++ tailWord_240165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240185 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 2, 8]
def baseStart_240185 : Nat := 118140960795 + 240185 * 2 ^ 59
def prefixEnd_240185 : Nat := 4983230072969 + 3 ^ 40 * 240185 * 2
def baseEnd_240185 : Nat := 41110117000082669594305

theorem tailTrace_240185 : CollatzResearch.WordTrace tailWord_240185 prefixEnd_240185 41110117000082669594305 := by
  unfold tailWord_240185
  simp only [CollatzResearch.WordTrace]
  refine ⟨8760266634858240177314009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5840177756572160118209339 8760266634858240177314009)
  ·
    refine ⟨6570199976143680132985507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8760266634858240177314009 6570199976143680132985507)
    ·
      refine ⟨9855299964215520199478261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6570199976143680132985507 9855299964215520199478261)
      ·
        refine ⟨923934371645205018701087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9855299964215520199478261 923934371645205018701087)
        ·
          refine ⟨1385901557467807528051631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 923934371645205018701087 1385901557467807528051631)
          ·
            refine ⟨2078852336201711292077447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1385901557467807528051631 2078852336201711292077447)
            ·
              refine ⟨3118278504302566938116171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2078852336201711292077447 3118278504302566938116171)
              ·
                refine ⟨4677417756453850407174257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3118278504302566938116171 4677417756453850407174257)
                ·
                  refine ⟨3508063317340387805380693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4677417756453850407174257 3508063317340387805380693)
                  ·
                    refine ⟨41110117000082669594305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3508063317340387805380693 41110117000082669594305)
                    ·
                      rfl

theorem cell23_240185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 8].length) (baseStart_240185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240185 prefixEnd_240185 := by exact prefixLift 240185
  have htrace : WordTrace (prefixWord ++ tailWord_240185) baseStart_240185 baseEnd_240185 := by
    simpa [prefixWord, tailWord_240185, baseEnd_240185] using wordTrace_append hprefix tailTrace_240185
  have hstable : (prefixWord ++ tailWord_240185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240185).length < 2 ^ (prefixWord ++ tailWord_240185).sum := by decide
  have hdescent : baseEnd_240185 < baseStart_240185 := by decide
  rcases family_descends (prefixWord ++ tailWord_240185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240192 : List Nat := [2, 1, 1, 2, 2, 2, 2, 2, 1, 6, 2]
def baseStart_240192 : Nat := 118140960795 + 240192 * 2 ^ 59
def prefixEnd_240192 : Nat := 4983230072969 + 3 ^ 40 * 240192 * 2
def baseEnd_240192 : Nat := 123333945364829481395383

theorem tailTrace_240192 : CollatzResearch.WordTrace tailWord_240192 prefixEnd_240192 123333945364829481395383 := by
  unfold tailWord_240192
  simp only [CollatzResearch.WordTrace]
  refine ⟨4380260972916440186409415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5840347963888586915212553 4380260972916440186409415)
  ·
    refine ⟨6570391459374660279614123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4380260972916440186409415 6570391459374660279614123)
    ·
      refine ⟨9855587189061990419421185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6570391459374660279614123 9855587189061990419421185)
      ·
        refine ⟨7391690391796492814565889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9855587189061990419421185 7391690391796492814565889)
        ·
          refine ⟨5543767793847369610924417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7391690391796492814565889 5543767793847369610924417)
          ·
            refine ⟨4157825845385527208193313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5543767793847369610924417 4157825845385527208193313)
            ·
              refine ⟨3118369384039145406144985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4157825845385527208193313 3118369384039145406144985)
              ·
                refine ⟨2338777038029359054608739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3118369384039145406144985 2338777038029359054608739)
                ·
                  refine ⟨3508165557044038581913109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2338777038029359054608739 3508165557044038581913109)
                  ·
                    refine ⟨164445260486439308527177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3508165557044038581913109 164445260486439308527177)
                    ·
                      refine ⟨123333945364829481395383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 164445260486439308527177 123333945364829481395383)
                      ·
                        rfl

theorem cell23_240192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 1, 6, 2].length) (baseStart_240192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240192 prefixEnd_240192 := by exact prefixLift 240192
  have htrace : WordTrace (prefixWord ++ tailWord_240192) baseStart_240192 baseEnd_240192 := by
    simpa [prefixWord, tailWord_240192, baseEnd_240192] using wordTrace_append hprefix tailTrace_240192
  have hstable : (prefixWord ++ tailWord_240192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240192).length < 2 ^ (prefixWord ++ tailWord_240192).sum := by decide
  have hdescent : baseEnd_240192 < baseStart_240192 := by decide
  rcases family_descends (prefixWord ++ tailWord_240192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240215 : List Nat := [1, 1, 3, 2, 2, 2, 1, 3, 8]
def baseStart_240215 : Nat := 118140960795 + 240215 * 2 ^ 59
def prefixEnd_240215 : Nat := 4983230072969 + 3 ^ 40 * 240215 * 2
def baseEnd_240215 : Nat := 13705083935542543489753

theorem tailTrace_240215 : CollatzResearch.WordTrace tailWord_240215 prefixEnd_240215 13705083935542543489753 := by
  unfold tailWord_240215
  simp only [CollatzResearch.WordTrace]
  refine ⟨8761360824749555300906099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5840907216499703533937399 8761360824749555300906099)
  ·
    refine ⟨13142041237124332951359149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8761360824749555300906099 13142041237124332951359149)
    ·
      refine ⟨4928265463921624856759681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13142041237124332951359149 4928265463921624856759681)
      ·
        refine ⟨3696199097941218642569761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4928265463921624856759681 3696199097941218642569761)
        ·
          refine ⟨2772149323455913981927321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3696199097941218642569761 2772149323455913981927321)
          ·
            refine ⟨2079111992591935486445491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2772149323455913981927321 2079111992591935486445491)
            ·
              refine ⟨3118667988887903229668237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2079111992591935486445491 3118667988887903229668237)
              ·
                refine ⟨1169500495832963711125589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3118667988887903229668237 1169500495832963711125589)
                ·
                  refine ⟨13705083935542543489753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1169500495832963711125589 13705083935542543489753)
                  ·
                    rfl

theorem cell23_240215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 8].length) (baseStart_240215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240215 prefixEnd_240215 := by exact prefixLift 240215
  have htrace : WordTrace (prefixWord ++ tailWord_240215) baseStart_240215 baseEnd_240215 := by
    simpa [prefixWord, tailWord_240215, baseEnd_240215] using wordTrace_append hprefix tailTrace_240215
  have hstable : (prefixWord ++ tailWord_240215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240215).length < 2 ^ (prefixWord ++ tailWord_240215).sum := by decide
  have hdescent : baseEnd_240215 < baseStart_240215 := by decide
  rcases family_descends (prefixWord ++ tailWord_240215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240255 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 5]
def baseStart_240255 : Nat := 118140960795 + 240255 * 2 ^ 59
def prefixEnd_240255 : Nat := 4983230072969 + 3 ^ 40 * 240255 * 2
def baseEnd_240255 : Nat := 123366294646062734907593

theorem tailTrace_240255 : CollatzResearch.WordTrace tailWord_240255 prefixEnd_240255 123366294646062734907593 := by
  unfold tailWord_240255
  simp only [CollatzResearch.WordTrace]
  refine ⟨8762819744604642132362219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5841879829736428088241479 8762819744604642132362219)
  ·
    refine ⟨13144229616906963198543329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8762819744604642132362219 13144229616906963198543329)
    ·
      refine ⟨9858172212680222398907497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13144229616906963198543329 9858172212680222398907497)
      ·
        refine ⟨7393629159510166799180623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9858172212680222398907497 7393629159510166799180623)
        ·
          refine ⟨11090443739265250198770935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7393629159510166799180623 11090443739265250198770935)
          ·
            refine ⟨16635665608897875298156403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11090443739265250198770935 16635665608897875298156403)
            ·
              refine ⟨24953498413346812947234605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16635665608897875298156403 24953498413346812947234605)
              ·
                refine ⟨9357561905005054855212977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24953498413346812947234605 9357561905005054855212977)
                ·
                  refine ⟨7018171428753791141409733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9357561905005054855212977 7018171428753791141409733)
                  ·
                    refine ⟨1315907142891335839014325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7018171428753791141409733 1315907142891335839014325)
                    ·
                      refine ⟨123366294646062734907593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1315907142891335839014325 123366294646062734907593)
                      ·
                        rfl

theorem cell23_240255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_240255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240255 prefixEnd_240255 := by exact prefixLift 240255
  have htrace : WordTrace (prefixWord ++ tailWord_240255) baseStart_240255 baseEnd_240255 := by
    simpa [prefixWord, tailWord_240255, baseEnd_240255] using wordTrace_append hprefix tailTrace_240255
  have hstable : (prefixWord ++ tailWord_240255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240255).length < 2 ^ (prefixWord ++ tailWord_240255).sum := by decide
  have hdescent : baseEnd_240255 < baseStart_240255 := by decide
  rcases family_descends (prefixWord ++ tailWord_240255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240286 : List Nat := [4, 3, 1, 1, 1, 1, 2, 2, 1, 5, 2]
def baseStart_240286 : Nat := 118140960795 + 240286 * 2 ^ 59
def prefixEnd_240286 : Nat := 4983230072969 + 3 ^ 40 * 240286 * 2
def baseEnd_240286 : Nat := 123382212546352113619951

theorem tailTrace_240286 : CollatzResearch.WordTrace tailWord_240286 prefixEnd_240286 123382212546352113619951 := by
  unfold tailWord_240286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1095493800936541803342589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5842633604994889617827141 1095493800936541803342589)
  ·
    refine ⟨410810175351203176253471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1095493800936541803342589 410810175351203176253471)
    ·
      refine ⟨616215263026804764380207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410810175351203176253471 616215263026804764380207)
      ·
        refine ⟨924322894540207146570311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 616215263026804764380207 924322894540207146570311)
        ·
          refine ⟨1386484341810310719855467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 924322894540207146570311 1386484341810310719855467)
          ·
            refine ⟨2079726512715466079783201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1386484341810310719855467 2079726512715466079783201)
            ·
              refine ⟨1559794884536599559837401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2079726512715466079783201 1559794884536599559837401)
              ·
                refine ⟨1169846163402449669878051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1559794884536599559837401 1169846163402449669878051)
                ·
                  refine ⟨1754769245103674504817077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1169846163402449669878051 1754769245103674504817077)
                  ·
                    refine ⟨164509616728469484826601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1754769245103674504817077 164509616728469484826601)
                    ·
                      refine ⟨123382212546352113619951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 164509616728469484826601 123382212546352113619951)
                      ·
                        rfl

theorem cell23_240286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_240286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240286 prefixEnd_240286 := by exact prefixLift 240286
  have htrace : WordTrace (prefixWord ++ tailWord_240286) baseStart_240286 baseEnd_240286 := by
    simpa [prefixWord, tailWord_240286, baseEnd_240286] using wordTrace_append hprefix tailTrace_240286
  have hstable : (prefixWord ++ tailWord_240286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240286).length < 2 ^ (prefixWord ++ tailWord_240286).sum := by decide
  have hdescent : baseEnd_240286 < baseStart_240286 := by decide
  rcases family_descends (prefixWord ++ tailWord_240286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240309 : List Nat := [1, 3, 3, 3, 1, 1, 2, 2, 1, 6]
def baseStart_240309 : Nat := 118140960795 + 240309 * 2 ^ 59
def prefixEnd_240309 : Nat := 4983230072969 + 3 ^ 40 * 240309 * 2
def baseEnd_240309 : Nat := 41131340867135174544115

theorem tailTrace_240309 : CollatzResearch.WordTrace tailWord_240309 prefixEnd_240309 41131340867135174544115 := by
  unfold tailWord_240309
  simp only [CollatzResearch.WordTrace]
  refine ⟨8764789286409009354827981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5843192857606006236551987 8764789286409009354827981)
  ·
    refine ⟨3286795982403378508060493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8764789286409009354827981 3286795982403378508060493)
    ·
      refine ⟨1232548493401266940522685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3286795982403378508060493 1232548493401266940522685)
      ·
        refine ⟨462205685025475102696007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1232548493401266940522685 462205685025475102696007)
        ·
          refine ⟨693308527538212654044011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462205685025475102696007 693308527538212654044011)
          ·
            refine ⟨1039962791307318981066017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693308527538212654044011 1039962791307318981066017)
            ·
              refine ⟨779972093480489235799513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1039962791307318981066017 779972093480489235799513)
              ·
                refine ⟨584979070110366926849635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 779972093480489235799513 584979070110366926849635)
                ·
                  refine ⟨877468605165550390274453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 584979070110366926849635 877468605165550390274453)
                  ·
                    refine ⟨41131340867135174544115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 877468605165550390274453 41131340867135174544115)
                    ·
                      rfl

theorem cell23_240309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_240309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240309 prefixEnd_240309 := by exact prefixLift 240309
  have htrace : WordTrace (prefixWord ++ tailWord_240309) baseStart_240309 baseEnd_240309 := by
    simpa [prefixWord, tailWord_240309, baseEnd_240309] using wordTrace_append hprefix tailTrace_240309
  have hstable : (prefixWord ++ tailWord_240309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240309).length < 2 ^ (prefixWord ++ tailWord_240309).sum := by decide
  have hdescent : baseEnd_240309 < baseStart_240309 := by decide
  rcases family_descends (prefixWord ++ tailWord_240309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240316 : List Nat := [2, 2, 2, 3, 1, 1, 1, 2, 5, 2, 2]
def baseStart_240316 : Nat := 118140960795 + 240316 * 2 ^ 59
def prefixEnd_240316 : Nat := 4983230072969 + 3 ^ 40 * 240316 * 2
def baseEnd_240316 : Nat := 123397616965986996244813

theorem tailTrace_240316 : CollatzResearch.WordTrace tailWord_240316 prefixEnd_240316 123397616965986996244813 := by
  unfold tailWord_240316
  simp only [CollatzResearch.WordTrace]
  refine ⟨4382522298691824775166401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5843363064922433033555201 4382522298691824775166401)
  ·
    refine ⟨3286891724018868581374801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4382522298691824775166401 3286891724018868581374801)
    ·
      refine ⟨2465168793014151436031101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3286891724018868581374801 2465168793014151436031101)
      ·
        refine ⟨924438297380306788511663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2465168793014151436031101 924438297380306788511663)
        ·
          refine ⟨1386657446070460182767495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 924438297380306788511663 1386657446070460182767495)
          ·
            refine ⟨2079986169105690274151243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1386657446070460182767495 2079986169105690274151243)
            ·
              refine ⟨3119979253658535411226865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2079986169105690274151243 3119979253658535411226865)
              ·
                refine ⟨2339984440243901558420149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3119979253658535411226865 2339984440243901558420149)
                ·
                  refine ⟨219373541272865771101889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2339984440243901558420149 219373541272865771101889)
                  ·
                    refine ⟨164530155954649328326417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 219373541272865771101889 164530155954649328326417)
                    ·
                      refine ⟨123397616965986996244813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 164530155954649328326417 123397616965986996244813)
                      ·
                        rfl

theorem cell23_240316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_240316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240316 prefixEnd_240316 := by exact prefixLift 240316
  have htrace : WordTrace (prefixWord ++ tailWord_240316) baseStart_240316 baseEnd_240316 := by
    simpa [prefixWord, tailWord_240316, baseEnd_240316] using wordTrace_append hprefix tailTrace_240316
  have hstable : (prefixWord ++ tailWord_240316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240316).length < 2 ^ (prefixWord ++ tailWord_240316).sum := by decide
  have hdescent : baseEnd_240316 < baseStart_240316 := by decide
  rcases family_descends (prefixWord ++ tailWord_240316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240366 : List Nat := [4, 1, 2, 1, 1, 3, 1, 2, 4, 1, 3]
def baseStart_240366 : Nat := 118140960795 + 240366 * 2 ^ 59
def prefixEnd_240366 : Nat := 4983230072969 + 3 ^ 40 * 240366 * 2
def baseEnd_240366 : Nat := 123423290998711800619583

theorem tailTrace_240366 : CollatzResearch.WordTrace tailWord_240366 prefixEnd_240366 123423290998711800619583 := by
  unfold tailWord_240366
  simp only [CollatzResearch.WordTrace]
  refine ⟨1095858530900313511206619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5844578831468338726435301 1095858530900313511206619)
  ·
    refine ⟨1643787796350470266809929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1095858530900313511206619 1643787796350470266809929)
    ·
      refine ⟨1232840847262852700107447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1643787796350470266809929 1232840847262852700107447)
      ·
        refine ⟨1849261270894279050161171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1232840847262852700107447 1849261270894279050161171)
        ·
          refine ⟨2773891906341418575241757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1849261270894279050161171 2773891906341418575241757)
          ·
            refine ⟨1040209464878031965715659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2773891906341418575241757 1040209464878031965715659)
            ·
              refine ⟨1560314197317047948573489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1040209464878031965715659 1560314197317047948573489)
              ·
                refine ⟨1170235647987785961430117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1560314197317047948573489 1170235647987785961430117)
                ·
                  refine ⟨219419183997709867768147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1170235647987785961430117 219419183997709867768147)
                  ·
                    refine ⟨329128775996564801652221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 219419183997709867768147 329128775996564801652221)
                    ·
                      refine ⟨123423290998711800619583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 329128775996564801652221 123423290998711800619583)
                      ·
                        rfl

theorem cell23_240366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_240366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240366 prefixEnd_240366 := by exact prefixLift 240366
  have htrace : WordTrace (prefixWord ++ tailWord_240366) baseStart_240366 baseEnd_240366 := by
    simpa [prefixWord, tailWord_240366, baseEnd_240366] using wordTrace_append hprefix tailTrace_240366
  have hstable : (prefixWord ++ tailWord_240366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240366).length < 2 ^ (prefixWord ++ tailWord_240366).sum := by decide
  have hdescent : baseEnd_240366 < baseStart_240366 := by decide
  rcases family_descends (prefixWord ++ tailWord_240366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240373 : List Nat := [1, 3, 6, 1, 1, 2, 9]
def baseStart_240373 : Nat := 118140960795 + 240373 * 2 ^ 59
def prefixEnd_240373 : Nat := 4983230072969 + 3 ^ 40 * 240373 * 2
def baseEnd_240373 : Nat := 1523788708188805842371

theorem tailTrace_240373 : CollatzResearch.WordTrace tailWord_240373 prefixEnd_240373 1523788708188805842371 := by
  unfold tailWord_240373
  simp only [CollatzResearch.WordTrace]
  refine ⟨8767123558177148285157773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5844749038784765523438515 8767123558177148285157773)
  ·
    refine ⟨3287671334316430606934165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8767123558177148285157773 3287671334316430606934165)
    ·
      refine ⟨154109593796082684700039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3287671334316430606934165 154109593796082684700039)
      ·
        refine ⟨231164390694124027050059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154109593796082684700039 231164390694124027050059)
        ·
          refine ⟨346746586041186040575089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231164390694124027050059 346746586041186040575089)
          ·
            refine ⟨260059939530889530431317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346746586041186040575089 260059939530889530431317)
            ·
              refine ⟨1523788708188805842371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 260059939530889530431317 1523788708188805842371)
              ·
                rfl

theorem cell23_240373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 9].length) (baseStart_240373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240373 prefixEnd_240373 := by exact prefixLift 240373
  have htrace : WordTrace (prefixWord ++ tailWord_240373) baseStart_240373 baseEnd_240373 := by
    simpa [prefixWord, tailWord_240373, baseEnd_240373] using wordTrace_append hprefix tailTrace_240373
  have hstable : (prefixWord ++ tailWord_240373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240373).length < 2 ^ (prefixWord ++ tailWord_240373).sum := by decide
  have hdescent : baseEnd_240373 < baseStart_240373 := by decide
  rcases family_descends (prefixWord ++ tailWord_240373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240376 : List Nat := [2, 1, 2, 1, 1, 2, 3, 5, 1, 3, 2]
def baseStart_240376 : Nat := 118140960795 + 240376 * 2 ^ 59
def prefixEnd_240376 : Nat := 4983230072969 + 3 ^ 40 * 240376 * 2
def baseEnd_240376 : Nat := 123428425805256761494537

theorem tailTrace_240376 : CollatzResearch.WordTrace tailWord_240376 prefixEnd_240376 123428425805256761494537 := by
  unfold tailWord_240376
  simp only [CollatzResearch.WordTrace]
  refine ⟨4383616488583139898758491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5844821984777519865011321 4383616488583139898758491)
  ·
    refine ⟨6575424732874709848137737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4383616488583139898758491 6575424732874709848137737)
    ·
      refine ⟨4931568549656032386103303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6575424732874709848137737 4931568549656032386103303)
      ·
        refine ⟨7397352824484048579154955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4931568549656032386103303 7397352824484048579154955)
        ·
          refine ⟨11096029236726072868732433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7397352824484048579154955 11096029236726072868732433)
          ·
            refine ⟨8322021927544554651549325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11096029236726072868732433 8322021927544554651549325)
            ·
              refine ⟨3120758222829207994330997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8322021927544554651549325 3120758222829207994330997)
              ·
                refine ⟨292571083390238249468531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3120758222829207994330997 292571083390238249468531)
                ·
                  refine ⟨438856625085357374202797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 292571083390238249468531 438856625085357374202797)
                  ·
                    refine ⟨164571234407009015326049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 438856625085357374202797 164571234407009015326049)
                    ·
                      refine ⟨123428425805256761494537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 164571234407009015326049 123428425805256761494537)
                      ·
                        rfl

theorem cell23_240376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5, 1, 3, 2].length) (baseStart_240376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240376 prefixEnd_240376 := by exact prefixLift 240376
  have htrace : WordTrace (prefixWord ++ tailWord_240376) baseStart_240376 baseEnd_240376 := by
    simpa [prefixWord, tailWord_240376, baseEnd_240376] using wordTrace_append hprefix tailTrace_240376
  have hstable : (prefixWord ++ tailWord_240376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240376).length < 2 ^ (prefixWord ++ tailWord_240376).sum := by decide
  have hdescent : baseEnd_240376 < baseStart_240376 := by decide
  rcases family_descends (prefixWord ++ tailWord_240376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240439 : List Nat := [1, 1, 3, 1, 2, 1, 4, 2, 2, 3, 3]
def baseStart_240439 : Nat := 118140960795 + 240439 * 2 ^ 59
def prefixEnd_240439 : Nat := 4983230072969 + 3 ^ 40 * 240439 * 2
def baseEnd_240439 : Nat := 123460775086490015006747

theorem tailTrace_240439 : CollatzResearch.WordTrace tailWord_240439 prefixEnd_240439 123460775086490015006747 := by
  unfold tailWord_240439
  simp only [CollatzResearch.WordTrace]
  refine ⟨8769530775938041557060371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5846353850625361038040247 8769530775938041557060371)
  ·
    refine ⟨13154296163907062335590557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8769530775938041557060371 13154296163907062335590557)
    ·
      refine ⟨4932861061465148375846459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13154296163907062335590557 4932861061465148375846459)
      ·
        refine ⟨7399291592197722563769689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4932861061465148375846459 7399291592197722563769689)
        ·
          refine ⟨5549468694148291922827267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7399291592197722563769689 5549468694148291922827267)
          ·
            refine ⟨8324203041222437884240901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5549468694148291922827267 8324203041222437884240901)
            ·
              refine ⟨1560788070229207103295169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8324203041222437884240901 1560788070229207103295169)
              ·
                refine ⟨1170591052671905327471377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1560788070229207103295169 1170591052671905327471377)
                ·
                  refine ⟨877943289503928995603533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1170591052671905327471377 877943289503928995603533)
                  ·
                    refine ⟨329228733563973373351325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 877943289503928995603533 329228733563973373351325)
                    ·
                      refine ⟨123460775086490015006747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 329228733563973373351325 123460775086490015006747)
                      ·
                        rfl

theorem cell23_240439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 3, 3].length) (baseStart_240439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240439 prefixEnd_240439 := by exact prefixLift 240439
  have htrace : WordTrace (prefixWord ++ tailWord_240439) baseStart_240439 baseEnd_240439 := by
    simpa [prefixWord, tailWord_240439, baseEnd_240439] using wordTrace_append hprefix tailTrace_240439
  have hstable : (prefixWord ++ tailWord_240439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240439).length < 2 ^ (prefixWord ++ tailWord_240439).sum := by decide
  have hdescent : baseEnd_240439 < baseStart_240439 := by decide
  rcases family_descends (prefixWord ++ tailWord_240439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240466 : List Nat := [3, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2]
def baseStart_240466 : Nat := 118140960795 + 240466 * 2 ^ 59
def prefixEnd_240466 : Nat := 4983230072969 + 3 ^ 40 * 240466 * 2
def baseEnd_240466 : Nat := 123474639064161409369123

theorem tailTrace_240466 : CollatzResearch.WordTrace tailWord_240466 prefixEnd_240466 123474639064161409369123 := by
  unfold tailWord_240466
  simp only [CollatzResearch.WordTrace]
  refine ⟨2192628886710056292073313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5847010364560150112195501 2192628886710056292073313)
  ·
    refine ⟨1644471665032542219054985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2192628886710056292073313 1644471665032542219054985)
    ·
      refine ⟨1233353748774406664291239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1644471665032542219054985 1233353748774406664291239)
      ·
        refine ⟨1850030623161609996436859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1233353748774406664291239 1850030623161609996436859)
        ·
          refine ⟨2775045934742414994655289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1850030623161609996436859 2775045934742414994655289)
          ·
            refine ⟨2081284451056811245991467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2775045934742414994655289 2081284451056811245991467)
            ·
              refine ⟨3121926676585216868987201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2081284451056811245991467 3121926676585216868987201)
              ·
                refine ⟨2341445007438912651740401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3121926676585216868987201 2341445007438912651740401)
                ·
                  refine ⟨1756083755579184488805301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2341445007438912651740401 1756083755579184488805301)
                  ·
                    refine ⟨164632852085548545825497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1756083755579184488805301 164632852085548545825497)
                    ·
                      refine ⟨123474639064161409369123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 164632852085548545825497 123474639064161409369123)
                      ·
                        rfl

theorem cell23_240466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2].length) (baseStart_240466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240466 prefixEnd_240466 := by exact prefixLift 240466
  have htrace : WordTrace (prefixWord ++ tailWord_240466) baseStart_240466 baseEnd_240466 := by
    simpa [prefixWord, tailWord_240466, baseEnd_240466] using wordTrace_append hprefix tailTrace_240466
  have hstable : (prefixWord ++ tailWord_240466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240466).length < 2 ^ (prefixWord ++ tailWord_240466).sum := by decide
  have hdescent : baseEnd_240466 < baseStart_240466 := by decide
  rcases family_descends (prefixWord ++ tailWord_240466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240476 : List Nat := [2, 2, 4, 2, 1, 2, 1, 1, 1, 7]
def baseStart_240476 : Nat := 118140960795 + 240476 * 2 ^ 59
def prefixEnd_240476 : Nat := 4983230072969 + 3 ^ 40 * 240476 * 2
def baseEnd_240476 : Nat := 41159924623568790081359

theorem tailTrace_240476 : CollatzResearch.WordTrace tailWord_240476 prefixEnd_240476 41159924623568790081359 := by
  unfold tailWord_240476
  simp only [CollatzResearch.WordTrace]
  refine ⟨4385440138401998438078641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5847253517869331250771521 4385440138401998438078641)
  ·
    refine ⟨3289080103801498828558981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4385440138401998438078641 3289080103801498828558981)
    ·
      refine ⟨616702519462781030354809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3289080103801498828558981 616702519462781030354809)
      ·
        refine ⟨462526889597085772766107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 616702519462781030354809 462526889597085772766107)
        ·
          refine ⟨693790334395628659149161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462526889597085772766107 693790334395628659149161)
          ·
            refine ⟨520342750796721494361871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 693790334395628659149161 520342750796721494361871)
            ·
              refine ⟨780514126195082241542807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 520342750796721494361871 780514126195082241542807)
              ·
                refine ⟨1170771189292623362314211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 780514126195082241542807 1170771189292623362314211)
                ·
                  refine ⟨1756156783938935043471317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1170771189292623362314211 1756156783938935043471317)
                  ·
                    refine ⟨41159924623568790081359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1756156783938935043471317 41159924623568790081359)
                    ·
                      rfl

theorem cell23_240476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_240476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240476 prefixEnd_240476 := by exact prefixLift 240476
  have htrace : WordTrace (prefixWord ++ tailWord_240476) baseStart_240476 baseEnd_240476 := by
    simpa [prefixWord, tailWord_240476, baseEnd_240476] using wordTrace_append hprefix tailTrace_240476
  have hstable : (prefixWord ++ tailWord_240476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240476).length < 2 ^ (prefixWord ++ tailWord_240476).sum := by decide
  have hdescent : baseEnd_240476 < baseStart_240476 := by decide
  rcases family_descends (prefixWord ++ tailWord_240476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240479 : List Nat := [1, 1, 2, 3, 1, 3, 3, 1, 1, 3, 4]
def baseStart_240479 : Nat := 118140960795 + 240479 * 2 ^ 59
def prefixEnd_240479 : Nat := 4983230072969 + 3 ^ 40 * 240479 * 2
def baseEnd_240479 : Nat := 123481314312669858506563

theorem tailTrace_240479 : CollatzResearch.WordTrace tailWord_240479 prefixEnd_240479 123481314312669858506563 := by
  unfold tailWord_240479
  simp only [CollatzResearch.WordTrace]
  refine ⟨8770989695793128388516491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5847326463862085592344327 8770989695793128388516491)
  ·
    refine ⟨13156484543689692582774737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8770989695793128388516491 13156484543689692582774737)
    ·
      refine ⟨9867363407767269437081053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13156484543689692582774737 9867363407767269437081053)
      ·
        refine ⟨3700261277912726038905395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9867363407767269437081053 3700261277912726038905395)
        ·
          refine ⟨5550391916869089058358093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3700261277912726038905395 5550391916869089058358093)
          ·
            refine ⟨2081396968825908396884285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5550391916869089058358093 2081396968825908396884285)
            ·
              refine ⟨780523863309715648831607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2081396968825908396884285 780523863309715648831607)
              ·
                refine ⟨1170785794964573473247411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 780523863309715648831607 1170785794964573473247411)
                ·
                  refine ⟨1756178692446860209871117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1170785794964573473247411 1756178692446860209871117)
                  ·
                    refine ⟨658567009667572578701669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1756178692446860209871117 658567009667572578701669)
                    ·
                      refine ⟨123481314312669858506563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 658567009667572578701669 123481314312669858506563)
                      ·
                        rfl

theorem cell23_240479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_240479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240479 prefixEnd_240479 := by exact prefixLift 240479
  have htrace : WordTrace (prefixWord ++ tailWord_240479) baseStart_240479 baseEnd_240479 := by
    simpa [prefixWord, tailWord_240479, baseEnd_240479] using wordTrace_append hprefix tailTrace_240479
  have hstable : (prefixWord ++ tailWord_240479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240479).length < 2 ^ (prefixWord ++ tailWord_240479).sum := by decide
  have hdescent : baseEnd_240479 < baseStart_240479 := by decide
  rcases family_descends (prefixWord ++ tailWord_240479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240496 : List Nat := [2, 1, 1, 1, 4, 1, 3, 2, 2, 4, 2]
def baseStart_240496 : Nat := 118140960795 + 240496 * 2 ^ 59
def prefixEnd_240496 : Nat := 4983230072969 + 3 ^ 40 * 240496 * 2
def baseEnd_240496 : Nat := 123490043483796291993985

theorem tailTrace_240496 : CollatzResearch.WordTrace tailWord_240496 prefixEnd_240496 123490043483796291993985 := by
  unfold tailWord_240496
  simp only [CollatzResearch.WordTrace]
  refine ⟨4385804868365770145942671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5847739824487693527923561 4385804868365770145942671)
  ·
    refine ⟨6578707302548655218914007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4385804868365770145942671 6578707302548655218914007)
    ·
      refine ⟨9868060953822982828371011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6578707302548655218914007 9868060953822982828371011)
      ·
        refine ⟨14802091430734474242556517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9868060953822982828371011 14802091430734474242556517)
        ·
          refine ⟨2775392143262713920479347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14802091430734474242556517 2775392143262713920479347)
          ·
            refine ⟨4163088214894070880719021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2775392143262713920479347 4163088214894070880719021)
            ·
              refine ⟨1561158080585276580269633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4163088214894070880719021 1561158080585276580269633)
              ·
                refine ⟨1170868560438957435202225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1561158080585276580269633 1170868560438957435202225)
                ·
                  refine ⟨878151420329218076401669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1170868560438957435202225 878151420329218076401669)
                  ·
                    refine ⟨164653391311728389325313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 878151420329218076401669 164653391311728389325313)
                    ·
                      refine ⟨123490043483796291993985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 164653391311728389325313 123490043483796291993985)
                      ·
                        rfl

theorem cell23_240496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 2, 4, 2].length) (baseStart_240496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240496 prefixEnd_240496 := by exact prefixLift 240496
  have htrace : WordTrace (prefixWord ++ tailWord_240496) baseStart_240496 baseEnd_240496 := by
    simpa [prefixWord, tailWord_240496, baseEnd_240496] using wordTrace_append hprefix tailTrace_240496
  have hstable : (prefixWord ++ tailWord_240496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240496).length < 2 ^ (prefixWord ++ tailWord_240496).sum := by decide
  have hdescent : baseEnd_240496 < baseStart_240496 := by decide
  rcases family_descends (prefixWord ++ tailWord_240496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240529 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 3]
def baseStart_240529 : Nat := 118140960795 + 240529 * 2 ^ 59
def prefixEnd_240529 : Nat := 4983230072969 + 3 ^ 40 * 240529 * 2
def baseEnd_240529 : Nat := 123506988345394662881333

theorem tailTrace_240529 : CollatzResearch.WordTrace tailWord_240529 prefixEnd_240529 123506988345394662881333 := by
  unfold tailWord_240529
  simp only [CollatzResearch.WordTrace]
  refine ⟨8772813345611986927836641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5848542230407991285224427 8772813345611986927836641)
  ·
    refine ⟨6579610009208990195877481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8772813345611986927836641 6579610009208990195877481)
    ·
      refine ⟨4934707506906742646908111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6579610009208990195877481 4934707506906742646908111)
      ·
        refine ⟨7402061260360113970362167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4934707506906742646908111 7402061260360113970362167)
        ·
          refine ⟨11103091890540170955543251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7402061260360113970362167 11103091890540170955543251)
          ·
            refine ⟨16654637835810256433314877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11103091890540170955543251 16654637835810256433314877)
            ·
              refine ⟨6245489188428846162493079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16654637835810256433314877 6245489188428846162493079)
              ·
                refine ⟨9368233782643269243739619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6245489188428846162493079 9368233782643269243739619)
                ·
                  refine ⟨14052350673964903865609429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9368233782643269243739619 14052350673964903865609429)
                  ·
                    refine ⟨329351968921052434350221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14052350673964903865609429 329351968921052434350221)
                    ·
                      refine ⟨123506988345394662881333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 329351968921052434350221 123506988345394662881333)
                      ·
                        rfl

theorem cell23_240529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 3].length) (baseStart_240529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240529 prefixEnd_240529 := by exact prefixLift 240529
  have htrace : WordTrace (prefixWord ++ tailWord_240529) baseStart_240529 baseEnd_240529 := by
    simpa [prefixWord, tailWord_240529, baseEnd_240529] using wordTrace_append hprefix tailTrace_240529
  have hstable : (prefixWord ++ tailWord_240529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240529).length < 2 ^ (prefixWord ++ tailWord_240529).sum := by decide
  have hdescent : baseEnd_240529 < baseStart_240529 := by decide
  rcases family_descends (prefixWord ++ tailWord_240529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240549 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 7, 5]
def baseStart_240549 : Nat := 118140960795 + 240549 * 2 ^ 59
def prefixEnd_240549 : Nat := 4983230072969 + 3 ^ 40 * 240549 * 2
def baseEnd_240549 : Nat := 41172419319494861543747

theorem tailTrace_240549 : CollatzResearch.WordTrace tailWord_240549 prefixEnd_240549 41172419319494861543747 := by
  unfold tailWord_240549
  simp only [CollatzResearch.WordTrace]
  refine ⟨8773542805539530343564701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5849028537026353562376467 8773542805539530343564701)
  ·
    refine ⟨3290078552077323878836763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8773542805539530343564701 3290078552077323878836763)
    ·
      refine ⟨4935117828115985818255145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3290078552077323878836763 4935117828115985818255145)
      ·
        refine ⟨3701338371086989363691359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4935117828115985818255145 3701338371086989363691359)
        ·
          refine ⟨5552007556630484045537039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3701338371086989363691359 5552007556630484045537039)
          ·
            refine ⟨8328011334945726068305559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5552007556630484045537039 8328011334945726068305559)
            ·
              refine ⟨12492017002418589102458339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8328011334945726068305559 12492017002418589102458339)
              ·
                refine ⟨18738025503627883653687509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12492017002418589102458339 18738025503627883653687509)
                ·
                  refine ⟨439172472741278523133301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18738025503627883653687509 439172472741278523133301)
                  ·
                    refine ⟨41172419319494861543747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 439172472741278523133301 41172419319494861543747)
                    ·
                      rfl

theorem cell23_240549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7, 5].length) (baseStart_240549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240549 prefixEnd_240549 := by exact prefixLift 240549
  have htrace : WordTrace (prefixWord ++ tailWord_240549) baseStart_240549 baseEnd_240549 := by
    simpa [prefixWord, tailWord_240549, baseEnd_240549] using wordTrace_append hprefix tailTrace_240549
  have hstable : (prefixWord ++ tailWord_240549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240549).length < 2 ^ (prefixWord ++ tailWord_240549).sum := by decide
  have hdescent : baseEnd_240549 < baseStart_240549 := by decide
  rcases family_descends (prefixWord ++ tailWord_240549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240557 : List Nat := [1, 5, 2, 3, 1, 2, 1, 1, 3, 4]
def baseStart_240557 : Nat := 118140960795 + 240557 * 2 ^ 59
def prefixEnd_240557 : Nat := 4983230072969 + 3 ^ 40 * 240557 * 2
def baseEnd_240557 : Nat := 41173788601240184443735

theorem tailTrace_240557 : CollatzResearch.WordTrace tailWord_240557 prefixEnd_240557 41173788601240184443735 := by
  unfold tailWord_240557
  simp only [CollatzResearch.WordTrace]
  refine ⟨8773834589510547709855925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5849223059673698473237283 8773834589510547709855925)
  ·
    refine ⟨822546992766613847798993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8773834589510547709855925 822546992766613847798993)
    ·
      refine ⟨616910244574960385849245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 822546992766613847798993 616910244574960385849245)
      ·
        refine ⟨231341341715610144693467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 616910244574960385849245 231341341715610144693467)
        ·
          refine ⟨347012012573415217040201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231341341715610144693467 347012012573415217040201)
          ·
            refine ⟨260259009430061412780151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347012012573415217040201 260259009430061412780151)
            ·
              refine ⟨390388514145092119170227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260259009430061412780151 390388514145092119170227)
              ·
                refine ⟨585582771217638178755341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390388514145092119170227 585582771217638178755341)
                ·
                  refine ⟨219593539206614317033253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 585582771217638178755341 219593539206614317033253)
                  ·
                    refine ⟨41173788601240184443735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 219593539206614317033253 41173788601240184443735)
                    ·
                      rfl

theorem cell23_240557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_240557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240557 prefixEnd_240557 := by exact prefixLift 240557
  have htrace : WordTrace (prefixWord ++ tailWord_240557) baseStart_240557 baseEnd_240557 := by
    simpa [prefixWord, tailWord_240557, baseEnd_240557] using wordTrace_append hprefix tailTrace_240557
  have hstable : (prefixWord ++ tailWord_240557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240557).length < 2 ^ (prefixWord ++ tailWord_240557).sum := by decide
  have hdescent : baseEnd_240557 < baseStart_240557 := by decide
  rcases family_descends (prefixWord ++ tailWord_240557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240590 : List Nat := [4, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2]
def baseStart_240590 : Nat := 118140960795 + 240590 * 2 ^ 59
def prefixEnd_240590 : Nat := 4983230072969 + 3 ^ 40 * 240590 * 2
def baseEnd_240590 : Nat := 123538310665318924218553

theorem tailTrace_240590 : CollatzResearch.WordTrace tailWord_240590 prefixEnd_240590 123538310665318924218553 := by
  unfold tailWord_240590
  simp only [CollatzResearch.WordTrace]
  refine ⟨1096879774798874293225903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5850025465593996230538149 1096879774798874293225903)
  ·
    refine ⟨1645319662198311439838855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1096879774798874293225903 1645319662198311439838855)
    ·
      refine ⟨2467979493297467159758283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1645319662198311439838855 2467979493297467159758283)
      ·
        refine ⟨3701969239946200739637425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2467979493297467159758283 3701969239946200739637425)
        ·
          refine ⟨2776476929959650554728069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3701969239946200739637425 2776476929959650554728069)
          ·
            refine ⟨520589424367434479011513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2776476929959650554728069 520589424367434479011513)
            ·
              refine ⟨390442068275575859258635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 520589424367434479011513 390442068275575859258635)
              ·
                refine ⟨585663102413363788887953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390442068275575859258635 585663102413363788887953)
                ·
                  refine ⟨439247326810022841665965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 585663102413363788887953 439247326810022841665965)
                  ·
                    refine ⟨164717747553758565624737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 439247326810022841665965 164717747553758565624737)
                    ·
                      refine ⟨123538310665318924218553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 164717747553758565624737 123538310665318924218553)
                      ·
                        rfl

theorem cell23_240590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2].length) (baseStart_240590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240590 prefixEnd_240590 := by exact prefixLift 240590
  have htrace : WordTrace (prefixWord ++ tailWord_240590) baseStart_240590 baseEnd_240590 := by
    simpa [prefixWord, tailWord_240590, baseEnd_240590] using wordTrace_append hprefix tailTrace_240590
  have hstable : (prefixWord ++ tailWord_240590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240590).length < 2 ^ (prefixWord ++ tailWord_240590).sum := by decide
  have hdescent : baseEnd_240590 < baseStart_240590 := by decide
  rcases family_descends (prefixWord ++ tailWord_240590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240596 : List Nat := [2, 4, 1, 2, 1, 2, 1, 1, 3, 6]
def baseStart_240596 : Nat := 118140960795 + 240596 * 2 ^ 59
def prefixEnd_240596 : Nat := 4983230072969 + 3 ^ 40 * 240596 * 2
def baseEnd_240596 : Nat := 41180463849748633581175

theorem tailTrace_240596 : CollatzResearch.WordTrace tailWord_240596 prefixEnd_240596 41180463849748633581175 := by
  unfold tailWord_240596
  simp only [CollatzResearch.WordTrace]
  refine ⟨4387628518184628685262821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5850171357579504913683761 4387628518184628685262821)
  ·
    refine ⟨822680347159617878486779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4387628518184628685262821 822680347159617878486779)
    ·
      refine ⟨1234020520739426817730169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 822680347159617878486779 1234020520739426817730169)
      ·
        refine ⟨925515390554570113297627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1234020520739426817730169 925515390554570113297627)
        ·
          refine ⟨1388273085831855169946441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 925515390554570113297627 1388273085831855169946441)
          ·
            refine ⟨1041204814373891377459831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1388273085831855169946441 1041204814373891377459831)
            ·
              refine ⟨1561807221560837066189747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1041204814373891377459831 1561807221560837066189747)
              ·
                refine ⟨2342710832341255599284621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1561807221560837066189747 2342710832341255599284621)
                ·
                  refine ⟨878516562127970849731733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2342710832341255599284621 878516562127970849731733)
                  ·
                    refine ⟨41180463849748633581175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 878516562127970849731733 41180463849748633581175)
                    ·
                      rfl

theorem cell23_240596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_240596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240596 prefixEnd_240596 := by exact prefixLift 240596
  have htrace : WordTrace (prefixWord ++ tailWord_240596) baseStart_240596 baseEnd_240596 := by
    simpa [prefixWord, tailWord_240596, baseEnd_240596] using wordTrace_append hprefix tailTrace_240596
  have hstable : (prefixWord ++ tailWord_240596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240596).length < 2 ^ (prefixWord ++ tailWord_240596).sum := by decide
  have hdescent : baseEnd_240596 < baseStart_240596 := by decide
  rcases family_descends (prefixWord ++ tailWord_240596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240599 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 6]
def baseStart_240599 : Nat := 118140960795 + 240599 * 2 ^ 59
def prefixEnd_240599 : Nat := 4983230072969 + 3 ^ 40 * 240599 * 2
def baseEnd_240599 : Nat := 123542931991209389006011

theorem tailTrace_240599 : CollatzResearch.WordTrace tailWord_240599 prefixEnd_240599 123542931991209389006011 := by
  unfold tailWord_240599
  simp only [CollatzResearch.WordTrace]
  refine ⟨8775366455358388882884851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5850244303572259255256567 8775366455358388882884851)
  ·
    refine ⟨13163049683037583324327277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8775366455358388882884851 13163049683037583324327277)
    ·
      refine ⟨4936143631139093746622729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13163049683037583324327277 4936143631139093746622729)
      ·
        refine ⟨3702107723354320309967047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4936143631139093746622729 3702107723354320309967047)
        ·
          refine ⟨5553161585031480464950571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3702107723354320309967047 5553161585031480464950571)
          ·
            refine ⟨8329742377547220697425857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5553161585031480464950571 8329742377547220697425857)
            ·
              refine ⟨6247306783160415523069393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8329742377547220697425857 6247306783160415523069393)
              ·
                refine ⟨4685480087370311642302045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6247306783160415523069393 4685480087370311642302045)
                ·
                  refine ⟨1757055032763866865863267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4685480087370311642302045 1757055032763866865863267)
                  ·
                    refine ⟨2635582549145800298794901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1757055032763866865863267 2635582549145800298794901)
                    ·
                      refine ⟨123542931991209389006011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2635582549145800298794901 123542931991209389006011)
                      ·
                        rfl

theorem cell23_240599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_240599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240599 prefixEnd_240599 := by exact prefixLift 240599
  have htrace : WordTrace (prefixWord ++ tailWord_240599) baseStart_240599 baseEnd_240599 := by
    simpa [prefixWord, tailWord_240599, baseEnd_240599] using wordTrace_append hprefix tailTrace_240599
  have hstable : (prefixWord ++ tailWord_240599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240599).length < 2 ^ (prefixWord ++ tailWord_240599).sum := by decide
  have hdescent : baseEnd_240599 < baseStart_240599 := by decide
  rcases family_descends (prefixWord ++ tailWord_240599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240630 : List Nat := [5, 1, 1, 1, 3, 1, 2, 3, 2, 4]
def baseStart_240630 : Nat := 118140960795 + 240630 * 2 ^ 59
def prefixEnd_240630 : Nat := 4983230072969 + 3 ^ 40 * 240630 * 2
def baseEnd_240630 : Nat := 41186283297166255906123

theorem tailTrace_240630 : CollatzResearch.WordTrace tailWord_240630 prefixEnd_240630 41186283297166255906123 := by
  unfold tailWord_240630
  simp only [CollatzResearch.WordTrace]
  refine ⟨548531069890380073578959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5850998078830720784842229 548531069890380073578959)
  ·
    refine ⟨822796604835570110368439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 548531069890380073578959 822796604835570110368439)
    ·
      refine ⟨1234194907253355165552659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 822796604835570110368439 1234194907253355165552659)
      ·
        refine ⟨1851292360880032748328989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1234194907253355165552659 1851292360880032748328989)
        ·
          refine ⟨694234635330012280623371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1851292360880032748328989 694234635330012280623371)
          ·
            refine ⟨1041351952995018420935057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 694234635330012280623371 1041351952995018420935057)
            ·
              refine ⟨781013964746263815701293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1041351952995018420935057 781013964746263815701293)
              ·
                refine ⟨292880236779848930887985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 781013964746263815701293 292880236779848930887985)
                ·
                  refine ⟨219660177584886698165989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 292880236779848930887985 219660177584886698165989)
                  ·
                    refine ⟨41186283297166255906123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 219660177584886698165989 41186283297166255906123)
                    ·
                      rfl

theorem cell23_240630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_240630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240630 prefixEnd_240630 := by exact prefixLift 240630
  have htrace : WordTrace (prefixWord ++ tailWord_240630) baseStart_240630 baseEnd_240630 := by
    simpa [prefixWord, tailWord_240630, baseEnd_240630] using wordTrace_append hprefix tailTrace_240630
  have hstable : (prefixWord ++ tailWord_240630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240630).length < 2 ^ (prefixWord ++ tailWord_240630).sum := by decide
  have hdescent : baseEnd_240630 < baseStart_240630 := by decide
  rcases family_descends (prefixWord ++ tailWord_240630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240654 : List Nat := [4, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2]
def baseStart_240654 : Nat := 118140960795 + 240654 * 2 ^ 59
def prefixEnd_240654 : Nat := 4983230072969 + 3 ^ 40 * 240654 * 2
def baseEnd_240654 : Nat := 123571173427206673818259

theorem tailTrace_240654 : CollatzResearch.WordTrace tailWord_240654 prefixEnd_240654 123571173427206673818259 := by
  unfold tailWord_240654
  simp only [CollatzResearch.WordTrace]
  refine ⟨1097171558769891659517127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5851581646772755517424677 1097171558769891659517127)
  ·
    refine ⟨1645757338154837489275691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1097171558769891659517127 1645757338154837489275691)
    ·
      refine ⟨2468636007232256233913537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1645757338154837489275691 2468636007232256233913537)
      ·
        refine ⟨1851477005424192175435153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2468636007232256233913537 1851477005424192175435153)
        ·
          refine ⟨1388607754068144131576365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1851477005424192175435153 1388607754068144131576365)
          ·
            refine ⟨520727907775554049341137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1388607754068144131576365 520727907775554049341137)
            ·
              refine ⟨390545930831665537005853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 520727907775554049341137 390545930831665537005853)
              ·
                refine ⟨146454724061874576377195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 390545930831665537005853 146454724061874576377195)
                ·
                  refine ⟨219682086092811864565793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146454724061874576377195 219682086092811864565793)
                  ·
                    refine ⟨164761564569608898424345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 219682086092811864565793 164761564569608898424345)
                    ·
                      refine ⟨123571173427206673818259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 164761564569608898424345 123571173427206673818259)
                      ·
                        rfl

theorem cell23_240654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2].length) (baseStart_240654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240654 prefixEnd_240654 := by exact prefixLift 240654
  have htrace : WordTrace (prefixWord ++ tailWord_240654) baseStart_240654 baseEnd_240654 := by
    simpa [prefixWord, tailWord_240654, baseEnd_240654] using wordTrace_append hprefix tailTrace_240654
  have hstable : (prefixWord ++ tailWord_240654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240654).length < 2 ^ (prefixWord ++ tailWord_240654).sum := by decide
  have hdescent : baseEnd_240654 < baseStart_240654 := by decide
  rcases family_descends (prefixWord ++ tailWord_240654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240697 : List Nat := [1, 2, 1, 5, 2, 2, 2, 2, 1, 3, 2]
def baseStart_240697 : Nat := 118140960795 + 240697 * 2 ^ 59
def prefixEnd_240697 : Nat := 4983230072969 + 3 ^ 40 * 240697 * 2
def baseEnd_240697 : Nat := 123593253095350005580561

theorem tailTrace_240697 : CollatzResearch.WordTrace tailWord_240697 prefixEnd_240697 123593253095350005580561 := by
  unfold tailWord_240697
  simp only [CollatzResearch.WordTrace]
  refine ⟨8778940809003351619952345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5852627206002234413301563 8778940809003351619952345)
  ·
    refine ⟨6584205606752513714964259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8778940809003351619952345 6584205606752513714964259)
    ·
      refine ⟨9876308410128770572446389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6584205606752513714964259 9876308410128770572446389)
      ·
        refine ⟨925903913449572241166849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9876308410128770572446389 925903913449572241166849)
        ·
          refine ⟨694427935087179180875137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 925903913449572241166849 694427935087179180875137)
          ·
            refine ⟨520820951315384385656353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 694427935087179180875137 520820951315384385656353)
            ·
              refine ⟨390615713486538289242265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 520820951315384385656353 390615713486538289242265)
              ·
                refine ⟨292961785114903716931699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 390615713486538289242265 292961785114903716931699)
                ·
                  refine ⟨439442677672355575397549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 292961785114903716931699 439442677672355575397549)
                  ·
                    refine ⟨164791004127133340774081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 439442677672355575397549 164791004127133340774081)
                    ·
                      refine ⟨123593253095350005580561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 164791004127133340774081 123593253095350005580561)
                      ·
                        rfl

theorem cell23_240697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_240697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240697 prefixEnd_240697 := by exact prefixLift 240697
  have htrace : WordTrace (prefixWord ++ tailWord_240697) baseStart_240697 baseEnd_240697 := by
    simpa [prefixWord, tailWord_240697, baseEnd_240697] using wordTrace_append hprefix tailTrace_240697
  have hstable : (prefixWord ++ tailWord_240697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240697).length < 2 ^ (prefixWord ++ tailWord_240697).sum := by decide
  have hdescent : baseEnd_240697 < baseStart_240697 := by decide
  rcases family_descends (prefixWord ++ tailWord_240697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240753 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 4, 5, 2]
def baseStart_240753 : Nat := 118140960795 + 240753 * 2 ^ 59
def prefixEnd_240753 : Nat := 4983230072969 + 3 ^ 40 * 240753 * 2
def baseEnd_240753 : Nat := 123622008012001786480303

theorem tailTrace_240753 : CollatzResearch.WordTrace tailWord_240753 prefixEnd_240753 123622008012001786480303 := by
  unfold tailWord_240753
  simp only [CollatzResearch.WordTrace]
  refine ⟨8780983296800473183990913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5853988864533648789327275 8780983296800473183990913)
  ·
    refine ⟨6585737472600354887993185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8780983296800473183990913 6585737472600354887993185)
    ·
      refine ⟨4939303104450266165994889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6585737472600354887993185 4939303104450266165994889)
      ·
        refine ⟨3704477328337699624496167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4939303104450266165994889 3704477328337699624496167)
        ·
          refine ⟨5556715992506549436744251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3704477328337699624496167 5556715992506549436744251)
          ·
            refine ⟨8335073988759824155116377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5556715992506549436744251 8335073988759824155116377)
            ·
              refine ⟨6251305491569868116337283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8335073988759824155116377 6251305491569868116337283)
              ·
                refine ⟨9376958237354802174505925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6251305491569868116337283 9376958237354802174505925)
                ·
                  refine ⟨1758179669504025407719861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9376958237354802174505925 1758179669504025407719861)
                  ·
                    refine ⟨164829344016002381973737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1758179669504025407719861 164829344016002381973737)
                    ·
                      refine ⟨123622008012001786480303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 164829344016002381973737 123622008012001786480303)
                      ·
                        rfl

theorem cell23_240753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 5, 2].length) (baseStart_240753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240753 prefixEnd_240753 := by exact prefixLift 240753
  have htrace : WordTrace (prefixWord ++ tailWord_240753) baseStart_240753 baseEnd_240753 := by
    simpa [prefixWord, tailWord_240753, baseEnd_240753] using wordTrace_append hprefix tailTrace_240753
  have hstable : (prefixWord ++ tailWord_240753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240753).length < 2 ^ (prefixWord ++ tailWord_240753).sum := by decide
  have hdescent : baseEnd_240753 < baseStart_240753 := by decide
  rcases family_descends (prefixWord ++ tailWord_240753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240800 : List Nat := [2, 1, 1, 4, 2, 1, 3, 1, 2, 4, 2]
def baseStart_240800 : Nat := 118140960795 + 240800 * 2 ^ 59
def prefixEnd_240800 : Nat := 4983230072969 + 3 ^ 40 * 240800 * 2
def baseEnd_240800 : Nat := 123646141602763102592587

theorem tailTrace_240800 : CollatzResearch.WordTrace tailWord_240800 prefixEnd_240800 123646141602763102592587 := by
  unfold tailWord_240800
  simp only [CollatzResearch.WordTrace]
  refine ⟨4391348763815100105475927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5855131685086800140634569 4391348763815100105475927)
  ·
    refine ⟨6587023145722650158213891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4391348763815100105475927 6587023145722650158213891)
    ·
      refine ⟨9880534718583975237320837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6587023145722650158213891 9880534718583975237320837)
      ·
        refine ⟨1852600259734495356997657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9880534718583975237320837 1852600259734495356997657)
        ·
          refine ⟨1389450194800871517748243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1852600259734495356997657 1389450194800871517748243)
          ·
            refine ⟨2084175292201307276622365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1389450194800871517748243 2084175292201307276622365)
            ·
              refine ⟨781565734575490228733387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2084175292201307276622365 781565734575490228733387)
              ·
                refine ⟨1172348601863235343100081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 781565734575490228733387 1172348601863235343100081)
                ·
                  refine ⟨879261451397426507325061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1172348601863235343100081 879261451397426507325061)
                  ·
                    refine ⟨164861522137017470123449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 879261451397426507325061 164861522137017470123449)
                    ·
                      refine ⟨123646141602763102592587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 164861522137017470123449 123646141602763102592587)
                      ·
                        rfl

theorem cell23_240800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 2, 4, 2].length) (baseStart_240800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240800 prefixEnd_240800 := by exact prefixLift 240800
  have htrace : WordTrace (prefixWord ++ tailWord_240800) baseStart_240800 baseEnd_240800 := by
    simpa [prefixWord, tailWord_240800, baseEnd_240800] using wordTrace_append hprefix tailTrace_240800
  have hstable : (prefixWord ++ tailWord_240800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240800).length < 2 ^ (prefixWord ++ tailWord_240800).sum := by decide
  have hdescent : baseEnd_240800 < baseStart_240800 := by decide
  rcases family_descends (prefixWord ++ tailWord_240800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240803 : List Nat := [1, 1, 1, 4, 1, 1, 1, 4, 4, 2, 3]
def baseStart_240803 : Nat := 118140960795 + 240803 * 2 ^ 59
def prefixEnd_240803 : Nat := 4983230072969 + 3 ^ 40 * 240803 * 2
def baseEnd_240803 : Nat := 123647682044726590855073

theorem tailTrace_240803 : CollatzResearch.WordTrace tailWord_240803 prefixEnd_240803 123647682044726590855073 := by
  unfold tailWord_240803
  simp only [CollatzResearch.WordTrace]
  refine ⟨8782806946619331723311063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5855204631079554482207375 8782806946619331723311063)
  ·
    refine ⟨13174210419928997584966595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8782806946619331723311063 13174210419928997584966595)
    ·
      refine ⟨19761315629893496377449893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13174210419928997584966595 19761315629893496377449893)
      ·
        refine ⟨3705246680605030570771855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19761315629893496377449893 3705246680605030570771855)
        ·
          refine ⟨5557870020907545856157783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3705246680605030570771855 5557870020907545856157783)
          ·
            refine ⟨8336805031361318784236675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5557870020907545856157783 8336805031361318784236675)
            ·
              refine ⟨12505207547041978176355013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8336805031361318784236675 12505207547041978176355013)
              ·
                refine ⟨2344726415070370908066565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12505207547041978176355013 2344726415070370908066565)
                ·
                  refine ⟨439636202825694545262481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2344726415070370908066565 439636202825694545262481)
                  ·
                    refine ⟨329727152119270908946861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 439636202825694545262481 329727152119270908946861)
                    ·
                      refine ⟨123647682044726590855073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 329727152119270908946861 123647682044726590855073)
                      ·
                        rfl

theorem cell23_240803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4, 2, 3].length) (baseStart_240803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240803 prefixEnd_240803 := by exact prefixLift 240803
  have htrace : WordTrace (prefixWord ++ tailWord_240803) baseStart_240803 baseEnd_240803 := by
    simpa [prefixWord, tailWord_240803, baseEnd_240803] using wordTrace_append hprefix tailTrace_240803
  have hstable : (prefixWord ++ tailWord_240803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240803).length < 2 ^ (prefixWord ++ tailWord_240803).sum := by decide
  have hdescent : baseEnd_240803 < baseStart_240803 := by decide
  rcases family_descends (prefixWord ++ tailWord_240803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240817 : List Nat := [1, 2, 2, 5, 1, 3, 1, 1, 2, 1, 4]
def baseStart_240817 : Nat := 118140960795 + 240817 * 2 ^ 59
def prefixEnd_240817 : Nat := 4983230072969 + 3 ^ 40 * 240817 * 2
def baseEnd_240817 : Nat := 123654870773889536080009

theorem tailTrace_240817 : CollatzResearch.WordTrace tailWord_240817 prefixEnd_240817 123654870773889536080009 := by
  unfold tailWord_240817
  simp only [CollatzResearch.WordTrace]
  refine ⟨8783317568568612114320705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5855545045712408076213803 8783317568568612114320705)
  ·
    refine ⟨6587488176426459085740529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8783317568568612114320705 6587488176426459085740529)
    ·
      refine ⟨4940616132319844314305397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6587488176426459085740529 4940616132319844314305397)
      ·
        refine ⟨463182762404985404466131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4940616132319844314305397 463182762404985404466131)
        ·
          refine ⟨694774143607478106699197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463182762404985404466131 694774143607478106699197)
          ·
            refine ⟨260540303852804290012199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 694774143607478106699197 260540303852804290012199)
            ·
              refine ⟨390810455779206435018299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260540303852804290012199 390810455779206435018299)
              ·
                refine ⟨586215683668809652527449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390810455779206435018299 586215683668809652527449)
                ·
                  refine ⟨439661762751607239395587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 586215683668809652527449 439661762751607239395587)
                  ·
                    refine ⟨659492644127410859093381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 439661762751607239395587 659492644127410859093381)
                    ·
                      refine ⟨123654870773889536080009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 659492644127410859093381 123654870773889536080009)
                      ·
                        rfl

theorem cell23_240817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_240817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240817 prefixEnd_240817 := by exact prefixLift 240817
  have htrace : WordTrace (prefixWord ++ tailWord_240817) baseStart_240817 baseEnd_240817 := by
    simpa [prefixWord, tailWord_240817, baseEnd_240817] using wordTrace_append hprefix tailTrace_240817
  have hstable : (prefixWord ++ tailWord_240817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240817).length < 2 ^ (prefixWord ++ tailWord_240817).sum := by decide
  have hdescent : baseEnd_240817 < baseStart_240817 := by decide
  rcases family_descends (prefixWord ++ tailWord_240817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240877 : List Nat := [1, 5, 1, 2, 2, 1, 2, 1, 1, 5, 2]
def baseStart_240877 : Nat := 118140960795 + 240877 * 2 ^ 59
def prefixEnd_240877 : Nat := 4983230072969 + 3 ^ 40 * 240877 * 2
def baseEnd_240877 : Nat := 123685679613159301329733

theorem tailTrace_240877 : CollatzResearch.WordTrace tailWord_240877 prefixEnd_240877 123685679613159301329733 := by
  unfold tailWord_240877
  simp only [CollatzResearch.WordTrace]
  refine ⟨8785505948351242361504885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5857003965567494907669923 8785505948351242361504885)
  ·
    refine ⟨823641182657928971391083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8785505948351242361504885 823641182657928971391083)
    ·
      refine ⟨1235461773986893457086625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 823641182657928971391083 1235461773986893457086625)
      ·
        refine ⟨926596330490170092814969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1235461773986893457086625 926596330490170092814969)
        ·
          refine ⟨694947247867627569611227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 926596330490170092814969 694947247867627569611227)
          ·
            refine ⟨1042420871801441354416841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 694947247867627569611227 1042420871801441354416841)
            ·
              refine ⟨781815653851081015812631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1042420871801441354416841 781815653851081015812631)
              ·
                refine ⟨1172723480776621523718947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 781815653851081015812631 1172723480776621523718947)
                ·
                  refine ⟨1759085221164932285578421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1172723480776621523718947 1759085221164932285578421)
                  ·
                    refine ⟨164914239484212401772977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1759085221164932285578421 164914239484212401772977)
                    ·
                      refine ⟨123685679613159301329733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 164914239484212401772977 123685679613159301329733)
                      ·
                        rfl

theorem cell23_240877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_240877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240877 prefixEnd_240877 := by exact prefixLift 240877
  have htrace : WordTrace (prefixWord ++ tailWord_240877) baseStart_240877 baseEnd_240877 := by
    simpa [prefixWord, tailWord_240877, baseEnd_240877] using wordTrace_append hprefix tailTrace_240877
  have hstable : (prefixWord ++ tailWord_240877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240877).length < 2 ^ (prefixWord ++ tailWord_240877).sum := by decide
  have hdescent : baseEnd_240877 < baseStart_240877 := by decide
  rcases family_descends (prefixWord ++ tailWord_240877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240890 : List Nat := [3, 1, 1, 1, 1, 4, 1, 5, 1, 1, 4]
def baseStart_240890 : Nat := 118140960795 + 240890 * 2 ^ 59
def prefixEnd_240890 : Nat := 4983230072969 + 3 ^ 40 * 240890 * 2
def baseEnd_240890 : Nat := 123692354861667750467173

theorem tailTrace_240890 : CollatzResearch.WordTrace tailWord_240890 prefixEnd_240890 123692354861667750467173 := by
  unfold tailWord_240890
  simp only [CollatzResearch.WordTrace]
  refine ⟨2196495024326036395432031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5857320064869430387818749 2196495024326036395432031)
  ·
    refine ⟨3294742536489054593148047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2196495024326036395432031 3294742536489054593148047)
    ·
      refine ⟨4942113804733581889722071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3294742536489054593148047 4942113804733581889722071)
      ·
        refine ⟨7413170707100372834583107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4942113804733581889722071 7413170707100372834583107)
        ·
          refine ⟨11119756060650559251874661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7413170707100372834583107 11119756060650559251874661)
          ·
            refine ⟨2084954261371979859726499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11119756060650559251874661 2084954261371979859726499)
            ·
              refine ⟨3127431392057969789589749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2084954261371979859726499 3127431392057969789589749)
              ·
                refine ⟨293196693005434667774039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3127431392057969789589749 293196693005434667774039)
                ·
                  refine ⟨439795039508152001661059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 293196693005434667774039 439795039508152001661059)
                  ·
                    refine ⟨659692559262228002491589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 439795039508152001661059 659692559262228002491589)
                    ·
                      refine ⟨123692354861667750467173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 659692559262228002491589 123692354861667750467173)
                      ·
                        rfl

theorem cell23_240890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5, 1, 1, 4].length) (baseStart_240890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240890 prefixEnd_240890 := by exact prefixLift 240890
  have htrace : WordTrace (prefixWord ++ tailWord_240890) baseStart_240890 baseEnd_240890 := by
    simpa [prefixWord, tailWord_240890, baseEnd_240890] using wordTrace_append hprefix tailTrace_240890
  have hstable : (prefixWord ++ tailWord_240890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240890).length < 2 ^ (prefixWord ++ tailWord_240890).sum := by decide
  have hdescent : baseEnd_240890 < baseStart_240890 := by decide
  rcases family_descends (prefixWord ++ tailWord_240890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240894 : List Nat := [4, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2]
def baseStart_240894 : Nat := 118140960795 + 240894 * 2 ^ 59
def prefixEnd_240894 : Nat := 4983230072969 + 3 ^ 40 * 240894 * 2
def baseEnd_240894 : Nat := 123694408784285734817155

theorem tailTrace_240894 : CollatzResearch.WordTrace tailWord_240894 prefixEnd_240894 123694408784285734817155 := by
  unfold tailWord_240894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1098265748661206783109217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5857417326193102843249157 1098265748661206783109217)
  ·
    refine ⟨823699311495905087331913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1098265748661206783109217 823699311495905087331913)
    ·
      refine ⟨617774483621928815498935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 823699311495905087331913 617774483621928815498935)
      ·
        refine ⟨926661725432893223248403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617774483621928815498935 926661725432893223248403)
        ·
          refine ⟨1389992588149339834872605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 926661725432893223248403 1389992588149339834872605)
          ·
            refine ⟨521247220556002438077227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1389992588149339834872605 521247220556002438077227)
            ·
              refine ⟨781870830834003657115841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 521247220556002438077227 781870830834003657115841)
              ·
                refine ⟨586403123125502742836881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 781870830834003657115841 586403123125502742836881)
                ·
                  refine ⟨439802342344127057127661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 586403123125502742836881 439802342344127057127661)
                  ·
                    refine ⟨164925878379047646422873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 439802342344127057127661 164925878379047646422873)
                    ·
                      refine ⟨123694408784285734817155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 164925878379047646422873 123694408784285734817155)
                      ·
                        rfl

theorem cell23_240894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_240894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240894 prefixEnd_240894 := by exact prefixLift 240894
  have htrace : WordTrace (prefixWord ++ tailWord_240894) baseStart_240894 baseEnd_240894 := by
    simpa [prefixWord, tailWord_240894, baseEnd_240894] using wordTrace_append hprefix tailTrace_240894
  have hstable : (prefixWord ++ tailWord_240894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240894).length < 2 ^ (prefixWord ++ tailWord_240894).sum := by decide
  have hdescent : baseEnd_240894 < baseStart_240894 := by decide
  rcases family_descends (prefixWord ++ tailWord_240894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240910 : List Nat := [4, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5]
def baseStart_240910 : Nat := 118140960795 + 240910 * 2 ^ 59
def prefixEnd_240910 : Nat := 4983230072969 + 3 ^ 40 * 240910 * 2
def baseEnd_240910 : Nat := 123702624474757672217081

theorem tailTrace_240910 : CollatzResearch.WordTrace tailWord_240910 prefixEnd_240910 123702624474757672217081 := by
  unfold tailWord_240910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1098338694653961124682023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5857806371487792664970789 1098338694653961124682023)
  ·
    refine ⟨1647508041980941687023035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1098338694653961124682023 1647508041980941687023035)
    ·
      refine ⟨2471262062971412530534553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1647508041980941687023035 2471262062971412530534553)
      ·
        refine ⟨1853446547228559397900915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2471262062971412530534553 1853446547228559397900915)
        ·
          refine ⟨2780169820842839096851373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1853446547228559397900915 2780169820842839096851373)
          ·
            refine ⟨1042563682816064661319265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2780169820842839096851373 1042563682816064661319265)
            ·
              refine ⟨781922762112048495989449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1042563682816064661319265 781922762112048495989449)
              ·
                refine ⟨586442071584036371992087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 781922762112048495989449 586442071584036371992087)
                ·
                  refine ⟨879663107376054557988131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 586442071584036371992087 879663107376054557988131)
                  ·
                    refine ⟨1319494661064081836982197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 879663107376054557988131 1319494661064081836982197)
                    ·
                      refine ⟨123702624474757672217081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1319494661064081836982197 123702624474757672217081)
                      ·
                        rfl

theorem cell23_240910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_240910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240910 prefixEnd_240910 := by exact prefixLift 240910
  have htrace : WordTrace (prefixWord ++ tailWord_240910) baseStart_240910 baseEnd_240910 := by
    simpa [prefixWord, tailWord_240910, baseEnd_240910] using wordTrace_append hprefix tailTrace_240910
  have hstable : (prefixWord ++ tailWord_240910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240910).length < 2 ^ (prefixWord ++ tailWord_240910).sum := by decide
  have hdescent : baseEnd_240910 < baseStart_240910 := by decide
  rcases family_descends (prefixWord ++ tailWord_240910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240913 : List Nat := [1, 2, 2, 1, 1, 4, 4, 8]
def baseStart_240913 : Nat := 118140960795 + 240913 * 2 ^ 59
def prefixEnd_240913 : Nat := 4983230072969 + 3 ^ 40 * 240913 * 2
def baseEnd_240913 : Nat := 4581635737656339277021

theorem tailTrace_240913 : CollatzResearch.WordTrace tailWord_240913 prefixEnd_240913 4581635737656339277021 := by
  unfold tailWord_240913
  simp only [CollatzResearch.WordTrace]
  refine ⟨8786818976220820509815393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5857879317480547006543595 8786818976220820509815393)
  ·
    refine ⟨6590114232165615382361545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8786818976220820509815393 6590114232165615382361545)
    ·
      refine ⟨4942585674124211536771159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6590114232165615382361545 4942585674124211536771159)
      ·
        refine ⟨7413878511186317305156739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4942585674124211536771159 7413878511186317305156739)
        ·
          refine ⟨11120817766779475957735109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7413878511186317305156739 11120817766779475957735109)
          ·
            refine ⟨2085153331271151742075333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11120817766779475957735109 2085153331271151742075333)
            ·
              refine ⟨390966249613340951639125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2085153331271151742075333 390966249613340951639125)
              ·
                refine ⟨4581635737656339277021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 390966249613340951639125 4581635737656339277021)
                ·
                  rfl

theorem cell23_240913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 8].length) (baseStart_240913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240913 prefixEnd_240913 := by exact prefixLift 240913
  have htrace : WordTrace (prefixWord ++ tailWord_240913) baseStart_240913 baseEnd_240913 := by
    simpa [prefixWord, tailWord_240913, baseEnd_240913] using wordTrace_append hprefix tailTrace_240913
  have hstable : (prefixWord ++ tailWord_240913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240913).length < 2 ^ (prefixWord ++ tailWord_240913).sum := by decide
  have hdescent : baseEnd_240913 < baseStart_240913 := by decide
  rcases family_descends (prefixWord ++ tailWord_240913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240927 : List Nat := [1, 1, 2, 4, 4, 1, 1, 1, 3, 2, 3]
def baseStart_240927 : Nat := 118140960795 + 240927 * 2 ^ 59
def prefixEnd_240927 : Nat := 4983230072969 + 3 ^ 40 * 240927 * 2
def baseEnd_240927 : Nat := 123711353645884105704503

theorem tailTrace_240927 : CollatzResearch.WordTrace tailWord_240927 prefixEnd_240927 123711353645884105704503 := by
  unfold tailWord_240927
  simp only [CollatzResearch.WordTrace]
  refine ⟨8787329598170100900825035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5858219732113400600550023 8787329598170100900825035)
  ·
    refine ⟨13180994397255151351237553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8787329598170100900825035 13180994397255151351237553)
    ·
      refine ⟨9885745797941363513428165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13180994397255151351237553 9885745797941363513428165)
      ·
        refine ⟨1853577337114005658767781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9885745797941363513428165 1853577337114005658767781)
        ·
          refine ⟨347545750708876061018959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1853577337114005658767781 347545750708876061018959)
          ·
            refine ⟨521318626063314091528439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347545750708876061018959 521318626063314091528439)
            ·
              refine ⟨781977939094971137292659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 521318626063314091528439 781977939094971137292659)
              ·
                refine ⟨1172966908642456705938989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 781977939094971137292659 1172966908642456705938989)
                ·
                  refine ⟨439862590740921264727121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1172966908642456705938989 439862590740921264727121)
                  ·
                    refine ⟨329896943055690948545341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 439862590740921264727121 329896943055690948545341)
                    ·
                      refine ⟨123711353645884105704503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 329896943055690948545341 123711353645884105704503)
                      ·
                        rfl

theorem cell23_240927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_240927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240927 prefixEnd_240927 := by exact prefixLift 240927
  have htrace : WordTrace (prefixWord ++ tailWord_240927) baseStart_240927 baseEnd_240927 := by
    simpa [prefixWord, tailWord_240927, baseEnd_240927] using wordTrace_append hprefix tailTrace_240927
  have hstable : (prefixWord ++ tailWord_240927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240927).length < 2 ^ (prefixWord ++ tailWord_240927).sum := by decide
  have hdescent : baseEnd_240927 < baseStart_240927 := by decide
  rcases family_descends (prefixWord ++ tailWord_240927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240941 : List Nat := [1, 5, 3, 1, 1, 2, 3, 1, 1, 1, 4]
def baseStart_240941 : Nat := 118140960795 + 240941 * 2 ^ 59
def prefixEnd_240941 : Nat := 4983230072969 + 3 ^ 40 * 240941 * 2
def baseEnd_240941 : Nat := 123718542375047050929439

theorem tailTrace_240941 : CollatzResearch.WordTrace tailWord_240941 prefixEnd_240941 123718542375047050929439 := by
  unfold tailWord_240941
  simp only [CollatzResearch.WordTrace]
  refine ⟨8787840220119381291834677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5858560146746254194556451 8787840220119381291834677)
  ·
    refine ⟨823860020636191996109501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8787840220119381291834677 823860020636191996109501)
    ·
      refine ⟨308947507738571998541063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 823860020636191996109501 308947507738571998541063)
      ·
        refine ⟨463421261607857997811595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308947507738571998541063 463421261607857997811595)
        ·
          refine ⟨695131892411786996717393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463421261607857997811595 695131892411786996717393)
          ·
            refine ⟨521348919308840247538045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 695131892411786996717393 521348919308840247538045)
            ·
              refine ⟨195505844740815092826767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 521348919308840247538045 195505844740815092826767)
              ·
                refine ⟨293258767111222639240151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195505844740815092826767 293258767111222639240151)
                ·
                  refine ⟨439888150666833958860227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 293258767111222639240151 439888150666833958860227)
                  ·
                    refine ⟨659832226000250938290341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 439888150666833958860227 659832226000250938290341)
                    ·
                      refine ⟨123718542375047050929439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 659832226000250938290341 123718542375047050929439)
                      ·
                        rfl

theorem cell23_240941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_240941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240941 prefixEnd_240941 := by exact prefixLift 240941
  have htrace : WordTrace (prefixWord ++ tailWord_240941) baseStart_240941 baseEnd_240941 := by
    simpa [prefixWord, tailWord_240941, baseEnd_240941] using wordTrace_append hprefix tailTrace_240941
  have hstable : (prefixWord ++ tailWord_240941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240941).length < 2 ^ (prefixWord ++ tailWord_240941).sum := by decide
  have hdescent : baseEnd_240941 < baseStart_240941 := by decide
  rcases family_descends (prefixWord ++ tailWord_240941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240967 : List Nat := [1, 1, 4, 1, 2, 3, 1, 2, 3, 3, 2]
def baseStart_240967 : Nat := 118140960795 + 240967 * 2 ^ 59
def prefixEnd_240967 : Nat := 4983230072969 + 3 ^ 40 * 240967 * 2
def baseEnd_240967 : Nat := 123731892872063949204319

theorem tailTrace_240967 : CollatzResearch.WordTrace tailWord_240967 prefixEnd_240967 123731892872063949204319 := by
  unfold tailWord_240967
  simp only [CollatzResearch.WordTrace]
  refine ⟨8788788518025187732281155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5859192345350125154854103 8788788518025187732281155)
  ·
    refine ⟨13183182777037781598421733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8788788518025187732281155 13183182777037781598421733)
    ·
      refine ⟨2471846770694584049704075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13183182777037781598421733 2471846770694584049704075)
      ·
        refine ⟨3707770156041876074556113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2471846770694584049704075 3707770156041876074556113)
        ·
          refine ⟨2780827617031407055917085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3707770156041876074556113 2780827617031407055917085)
          ·
            refine ⟨1042810356386777645968907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2780827617031407055917085 1042810356386777645968907)
            ·
              refine ⟨1564215534580166468953361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1042810356386777645968907 1564215534580166468953361)
              ·
                refine ⟨1173161650935124851715021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1564215534580166468953361 1173161650935124851715021)
                ·
                  refine ⟨439935619100671819393133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1173161650935124851715021 439935619100671819393133)
                  ·
                    refine ⟨164975857162751932272425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 439935619100671819393133 164975857162751932272425)
                    ·
                      refine ⟨123731892872063949204319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 164975857162751932272425 123731892872063949204319)
                      ·
                        rfl

theorem cell23_240967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3, 3, 2].length) (baseStart_240967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240967 prefixEnd_240967 := by exact prefixLift 240967
  have htrace : WordTrace (prefixWord ++ tailWord_240967) baseStart_240967 baseEnd_240967 := by
    simpa [prefixWord, tailWord_240967, baseEnd_240967] using wordTrace_append hprefix tailTrace_240967
  have hstable : (prefixWord ++ tailWord_240967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240967).length < 2 ^ (prefixWord ++ tailWord_240967).sum := by decide
  have hdescent : baseEnd_240967 < baseStart_240967 := by decide
  rcases family_descends (prefixWord ++ tailWord_240967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240980 : List Nat := [2, 4, 1, 1, 2, 1, 1, 2, 2, 3, 4]
def baseStart_240980 : Nat := 118140960795 + 240980 * 2 ^ 59
def prefixEnd_240980 : Nat := 4983230072969 + 3 ^ 40 * 240980 * 2
def baseEnd_240980 : Nat := 123738568120572398341759

theorem tailTrace_240980 : CollatzResearch.WordTrace tailWord_240980 prefixEnd_240980 123738568120572398341759 := by
  unfold tailWord_240980
  simp only [CollatzResearch.WordTrace]
  refine ⟨4394631333489045476252197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5859508444652060635002929 4394631333489045476252197)
  ·
    refine ⟨823993375029196026797287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4394631333489045476252197 823993375029196026797287)
    ·
      refine ⟨1235990062543794040195931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 823993375029196026797287 1235990062543794040195931)
      ·
        refine ⟨1853985093815691060293897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1235990062543794040195931 1853985093815691060293897)
        ·
          refine ⟨1390488820361768295220423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1853985093815691060293897 1390488820361768295220423)
          ·
            refine ⟨2085733230542652442830635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1390488820361768295220423 2085733230542652442830635)
            ·
              refine ⟨3128599845813978664245953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2085733230542652442830635 3128599845813978664245953)
              ·
                refine ⟨2346449884360483998184465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3128599845813978664245953 2346449884360483998184465)
                ·
                  refine ⟨1759837413270362998638349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2346449884360483998184465 1759837413270362998638349)
                  ·
                    refine ⟨659939029976386124489381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1759837413270362998638349 659939029976386124489381)
                    ·
                      refine ⟨123738568120572398341759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 659939029976386124489381 123738568120572398341759)
                      ·
                        rfl

theorem cell23_240980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_240980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240980 prefixEnd_240980 := by exact prefixLift 240980
  have htrace : WordTrace (prefixWord ++ tailWord_240980) baseStart_240980 baseEnd_240980 := by
    simpa [prefixWord, tailWord_240980, baseEnd_240980] using wordTrace_append hprefix tailTrace_240980
  have hstable : (prefixWord ++ tailWord_240980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240980).length < 2 ^ (prefixWord ++ tailWord_240980).sum := by decide
  have hdescent : baseEnd_240980 < baseStart_240980 := by decide
  rcases family_descends (prefixWord ++ tailWord_240980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240997 : List Nat := [1, 3, 1, 3, 1, 2, 1, 4, 1, 4, 2]
def baseStart_240997 : Nat := 118140960795 + 240997 * 2 ^ 59
def prefixEnd_240997 : Nat := 4983230072969 + 3 ^ 40 * 240997 * 2
def baseEnd_240997 : Nat := 123747297291698831829181

theorem tailTrace_240997 : CollatzResearch.WordTrace tailWord_240997 prefixEnd_240997 123747297291698831829181 := by
  unfold tailWord_240997
  simp only [CollatzResearch.WordTrace]
  refine ⟨8789882707916502855873245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5859921805277668570582163 8789882707916502855873245)
  ·
    refine ⟨3296206015468688570952467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8789882707916502855873245 3296206015468688570952467)
    ·
      refine ⟨4944309023203032856428701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3296206015468688570952467 4944309023203032856428701)
      ·
        refine ⟨1854115883701137321160763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4944309023203032856428701 1854115883701137321160763)
        ·
          refine ⟨2781173825551705981741145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1854115883701137321160763 2781173825551705981741145)
          ·
            refine ⟨2085880369163779486305859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2781173825551705981741145 2085880369163779486305859)
            ·
              refine ⟨3128820553745669229458789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2085880369163779486305859 3128820553745669229458789)
              ·
                refine ⟨586653853827312980523523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3128820553745669229458789 586653853827312980523523)
                ·
                  refine ⟨879980780740969470785285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 586653853827312980523523 879980780740969470785285)
                  ·
                    refine ⟨164996396388931775772241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 879980780740969470785285 164996396388931775772241)
                    ·
                      refine ⟨123747297291698831829181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 164996396388931775772241 123747297291698831829181)
                      ·
                        rfl

theorem cell23_240997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 4, 2].length) (baseStart_240997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_240997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_240997 prefixEnd_240997 := by exact prefixLift 240997
  have htrace : WordTrace (prefixWord ++ tailWord_240997) baseStart_240997 baseEnd_240997 := by
    simpa [prefixWord, tailWord_240997, baseEnd_240997] using wordTrace_append hprefix tailTrace_240997
  have hstable : (prefixWord ++ tailWord_240997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240997).length < 2 ^ (prefixWord ++ tailWord_240997).sum := by decide
  have hdescent : baseEnd_240997 < baseStart_240997 := by decide
  rcases family_descends (prefixWord ++ tailWord_240997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241010 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 4, 2, 4]
def baseStart_241010 : Nat := 118140960795 + 241010 * 2 ^ 59
def prefixEnd_241010 : Nat := 4983230072969 + 3 ^ 40 * 241010 * 2
def baseEnd_241010 : Nat := 123753972540207280966621

theorem tailTrace_241010 : CollatzResearch.WordTrace tailWord_241010 prefixEnd_241010 123753972540207280966621 := by
  unfold tailWord_241010
  simp only [CollatzResearch.WordTrace]
  refine ⟨2197589214217351519024121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5860237904579604050730989 2197589214217351519024121)
  ·
    refine ⟨1648191910663013639268091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2197589214217351519024121 1648191910663013639268091)
    ·
      refine ⟨2472287865994520458902137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1648191910663013639268091 2472287865994520458902137)
      ·
        refine ⟨1854215899495890344176603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2472287865994520458902137 1854215899495890344176603)
        ·
          refine ⟨2781323849243835516264905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1854215899495890344176603 2781323849243835516264905)
          ·
            refine ⟨2085992886932876637198679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2781323849243835516264905 2085992886932876637198679)
            ·
              refine ⟨3128989330399314955798019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2085992886932876637198679 3128989330399314955798019)
              ·
                refine ⟨4693483995598972433697029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3128989330399314955798019 4693483995598972433697029)
                ·
                  refine ⟨880028249174807331318193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4693483995598972433697029 880028249174807331318193)
                  ·
                    refine ⟨660021186881105498488645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 880028249174807331318193 660021186881105498488645)
                    ·
                      refine ⟨123753972540207280966621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 660021186881105498488645 123753972540207280966621)
                      ·
                        rfl

theorem cell23_241010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_241010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_241010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_241010 prefixEnd_241010 := by exact prefixLift 241010
  have htrace : WordTrace (prefixWord ++ tailWord_241010) baseStart_241010 baseEnd_241010 := by
    simpa [prefixWord, tailWord_241010, baseEnd_241010] using wordTrace_append hprefix tailTrace_241010
  have hstable : (prefixWord ++ tailWord_241010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241010).length < 2 ^ (prefixWord ++ tailWord_241010).sum := by decide
  have hdescent : baseEnd_241010 < baseStart_241010 := by decide
  rcases family_descends (prefixWord ++ tailWord_241010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241020 : List Nat := [2, 2, 2, 1, 1, 1, 6, 1, 7]
def baseStart_241020 : Nat := 118140960795 + 241020 * 2 ^ 59
def prefixEnd_241020 : Nat := 4983230072969 + 3 ^ 40 * 241020 * 2
def baseEnd_241020 : Nat := 13751011927416915760175

theorem tailTrace_241020 : CollatzResearch.WordTrace tailWord_241020 prefixEnd_241020 13751011927416915760175 := by
  unfold tailWord_241020
  simp only [CollatzResearch.WordTrace]
  refine ⟨4395360793416588891980257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5860481057888785189307009 4395360793416588891980257)
  ·
    refine ⟨3296520595062441668985193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4395360793416588891980257 3296520595062441668985193)
    ·
      refine ⟨2472390446296831251738895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3296520595062441668985193 2472390446296831251738895)
      ·
        refine ⟨3708585669445246877608343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2472390446296831251738895 3708585669445246877608343)
        ·
          refine ⟨5562878504167870316412515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3708585669445246877608343 5562878504167870316412515)
          ·
            refine ⟨8344317756251805474618773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5562878504167870316412515 8344317756251805474618773)
            ·
              refine ⟨391139894824303381622755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8344317756251805474618773 391139894824303381622755)
              ·
                refine ⟨586709842236455072434133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 391139894824303381622755 586709842236455072434133)
                ·
                  refine ⟨13751011927416915760175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 586709842236455072434133 13751011927416915760175)
                  ·
                    rfl

theorem cell23_241020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 7].length) (baseStart_241020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_241020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_241020 prefixEnd_241020 := by exact prefixLift 241020
  have htrace : WordTrace (prefixWord ++ tailWord_241020) baseStart_241020 baseEnd_241020 := by
    simpa [prefixWord, tailWord_241020, baseEnd_241020] using wordTrace_append hprefix tailTrace_241020
  have hstable : (prefixWord ++ tailWord_241020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241020).length < 2 ^ (prefixWord ++ tailWord_241020).sum := by decide
  have hdescent : baseEnd_241020 < baseStart_241020 := by decide
  rcases family_descends (prefixWord ++ tailWord_241020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241023 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 8]
def baseStart_241023 : Nat := 118140960795 + 241023 * 2 ^ 59
def prefixEnd_241023 : Nat := 4983230072969 + 3 ^ 40 * 241023 * 2
def baseEnd_241023 : Nat := 123760647788715730104061

theorem tailTrace_241023 : CollatzResearch.WordTrace tailWord_241023 prefixEnd_241023 123760647788715730104061 := by
  unfold tailWord_241023
  simp only [CollatzResearch.WordTrace]
  refine ⟨8790831005822309296319723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5860554003881539530879815 8790831005822309296319723)
  ·
    refine ⟨13186246508733463944479585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8790831005822309296319723 13186246508733463944479585)
    ·
      refine ⟨9889684881550097958359689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13186246508733463944479585 9889684881550097958359689)
      ·
        refine ⟨7417263661162573468769767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9889684881550097958359689 7417263661162573468769767)
        ·
          refine ⟨11125895491743860203154651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7417263661162573468769767 11125895491743860203154651)
          ·
            refine ⟨16688843237615790304731977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11125895491743860203154651 16688843237615790304731977)
            ·
              refine ⟨12516632428211842728548983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16688843237615790304731977 12516632428211842728548983)
              ·
                refine ⟨18774948642317764092823475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12516632428211842728548983 18774948642317764092823475)
                ·
                  refine ⟨28162422963476646139235213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18774948642317764092823475 28162422963476646139235213)
                  ·
                    refine ⟨10560908611303742302213205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28162422963476646139235213 10560908611303742302213205)
                    ·
                      refine ⟨123760647788715730104061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 10560908611303742302213205 123760647788715730104061)
                      ·
                        rfl

theorem cell23_241023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_241023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_241023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_241023 prefixEnd_241023 := by exact prefixLift 241023
  have htrace : WordTrace (prefixWord ++ tailWord_241023) baseStart_241023 baseEnd_241023 := by
    simpa [prefixWord, tailWord_241023, baseEnd_241023] using wordTrace_append hprefix tailTrace_241023
  have hstable : (prefixWord ++ tailWord_241023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241023).length < 2 ^ (prefixWord ++ tailWord_241023).sum := by decide
  have hdescent : baseEnd_241023 < baseStart_241023 := by decide
  rcases family_descends (prefixWord ++ tailWord_241023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241050 : List Nat := [3, 1, 1, 4, 1, 1, 1, 3, 1, 7]
def baseStart_241050 : Nat := 118140960795 + 241050 * 2 ^ 59
def prefixEnd_241050 : Nat := 4983230072969 + 3 ^ 40 * 241050 * 2
def baseEnd_241050 : Nat := 41258170588795708155479

theorem tailTrace_241050 : CollatzResearch.WordTrace tailWord_241050 prefixEnd_241050 41258170588795708155479 := by
  unfold tailWord_241050
  simp only [CollatzResearch.WordTrace]
  refine ⟨2197953944181123226888151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5861210517816328605035069 2197953944181123226888151)
  ·
    refine ⟨3296930916271684840332227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2197953944181123226888151 3296930916271684840332227)
    ·
      refine ⟨4945396374407527260498341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3296930916271684840332227 4945396374407527260498341)
      ·
        refine ⟨927261820201411361343439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4945396374407527260498341 927261820201411361343439)
        ·
          refine ⟨1390892730302117042015159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 927261820201411361343439 1390892730302117042015159)
          ·
            refine ⟨2086339095453175563022739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1390892730302117042015159 2086339095453175563022739)
            ·
              refine ⟨3129508643179763344534109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2086339095453175563022739 3129508643179763344534109)
              ·
                refine ⟨1173565741192411254200291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3129508643179763344534109 1173565741192411254200291)
                ·
                  refine ⟨1760348611788616881300437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1173565741192411254200291 1760348611788616881300437)
                  ·
                    refine ⟨41258170588795708155479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1760348611788616881300437 41258170588795708155479)
                    ·
                      rfl

theorem cell23_241050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 1, 7].length) (baseStart_241050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_241050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_241050 prefixEnd_241050 := by exact prefixLift 241050
  have htrace : WordTrace (prefixWord ++ tailWord_241050) baseStart_241050 baseEnd_241050 := by
    simpa [prefixWord, tailWord_241050, baseEnd_241050] using wordTrace_append hprefix tailTrace_241050
  have hstable : (prefixWord ++ tailWord_241050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241050).length < 2 ^ (prefixWord ++ tailWord_241050).sum := by decide
  have hdescent : baseEnd_241050 < baseStart_241050 := by decide
  rcases family_descends (prefixWord ++ tailWord_241050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241060 : List Nat := [2, 3, 1, 2, 1, 1, 1, 4, 1, 2, 5]
def baseStart_241060 : Nat := 118140960795 + 241060 * 2 ^ 59
def prefixEnd_241060 : Nat := 4983230072969 + 3 ^ 40 * 241060 * 2
def baseEnd_241060 : Nat := 123779646572932085341391

theorem tailTrace_241060 : CollatzResearch.WordTrace tailWord_241060 prefixEnd_241060 123779646572932085341391 := by
  unfold tailWord_241060
  simp only [CollatzResearch.WordTrace]
  refine ⟨4396090253344132307708317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5861453671125509743611089 4396090253344132307708317)
  ·
    refine ⟨1648533845004049615390619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4396090253344132307708317 1648533845004049615390619)
    ·
      refine ⟨2472800767506074423085929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1648533845004049615390619 2472800767506074423085929)
      ·
        refine ⟨1854600575629555817314447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2472800767506074423085929 1854600575629555817314447)
        ·
          refine ⟨2781900863444333725971671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1854600575629555817314447 2781900863444333725971671)
          ·
            refine ⟨4172851295166500588957507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2781900863444333725971671 4172851295166500588957507)
            ·
              refine ⟨6259276942749750883436261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4172851295166500588957507 6259276942749750883436261)
              ·
                refine ⟨1173614426765578290644299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6259276942749750883436261 1173614426765578290644299)
                ·
                  refine ⟨1760421640148367435966449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1173614426765578290644299 1760421640148367435966449)
                  ·
                    refine ⟨1320316230111275576974837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1760421640148367435966449 1320316230111275576974837)
                    ·
                      refine ⟨123779646572932085341391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1320316230111275576974837 123779646572932085341391)
                      ·
                        rfl

theorem cell23_241060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_241060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_241060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_241060 prefixEnd_241060 := by exact prefixLift 241060
  have htrace : WordTrace (prefixWord ++ tailWord_241060) baseStart_241060 baseEnd_241060 := by
    simpa [prefixWord, tailWord_241060, baseEnd_241060] using wordTrace_append hprefix tailTrace_241060
  have hstable : (prefixWord ++ tailWord_241060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241060).length < 2 ^ (prefixWord ++ tailWord_241060).sum := by decide
  have hdescent : baseEnd_241060 < baseStart_241060 := by decide
  rcases family_descends (prefixWord ++ tailWord_241060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241077 : List Nat := [1, 3, 3, 2, 2, 2, 1, 1, 1, 2, 5]
def baseStart_241077 : Nat := 118140960795 + 241077 * 2 ^ 59
def prefixEnd_241077 : Nat := 4983230072969 + 3 ^ 40 * 241077 * 2
def baseEnd_241077 : Nat := 123788375744058518828813

theorem tailTrace_241077 : CollatzResearch.WordTrace tailWord_241077 prefixEnd_241077 123788375744058518828813 := by
  unfold tailWord_241077
  simp only [CollatzResearch.WordTrace]
  refine ⟨8792800547626676518785485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5861867031751117679190323 8792800547626676518785485)
  ·
    refine ⟨3297300205360003694544557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8792800547626676518785485 3297300205360003694544557)
    ·
      refine ⟨1236487577010001385454209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3297300205360003694544557 1236487577010001385454209)
      ·
        refine ⟨927365682757501039090657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1236487577010001385454209 927365682757501039090657)
        ·
          refine ⟨695524262068125779317993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 927365682757501039090657 695524262068125779317993)
          ·
            refine ⟨521643196551094334488495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 695524262068125779317993 521643196551094334488495)
            ·
              refine ⟨782464794826641501732743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 521643196551094334488495 782464794826641501732743)
              ·
                refine ⟨1173697192239962252599115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 782464794826641501732743 1173697192239962252599115)
                ·
                  refine ⟨1760545788359943378898673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1173697192239962252599115 1760545788359943378898673)
                  ·
                    refine ⟨1320409341269957534174005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1760545788359943378898673 1320409341269957534174005)
                    ·
                      refine ⟨123788375744058518828813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1320409341269957534174005 123788375744058518828813)
                      ·
                        rfl

theorem cell23_241077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_241077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_241077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_241077 prefixEnd_241077 := by exact prefixLift 241077
  have htrace : WordTrace (prefixWord ++ tailWord_241077) baseStart_241077 baseEnd_241077 := by
    simpa [prefixWord, tailWord_241077, baseEnd_241077] using wordTrace_append hprefix tailTrace_241077
  have hstable : (prefixWord ++ tailWord_241077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241077).length < 2 ^ (prefixWord ++ tailWord_241077).sum := by decide
  have hdescent : baseEnd_241077 < baseStart_241077 := by decide
  rcases family_descends (prefixWord ++ tailWord_241077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241087 : List Nat := [1, 1, 2, 2, 2, 1, 1, 5, 2, 4, 2]
def baseStart_241087 : Nat := 118140960795 + 241087 * 2 ^ 59
def prefixEnd_241087 : Nat := 4983230072969 + 3 ^ 40 * 241087 * 2
def baseEnd_241087 : Nat := 123793510550603479703767

theorem tailTrace_241087 : CollatzResearch.WordTrace tailWord_241087 prefixEnd_241087 123793510550603479703767 := by
  unfold tailWord_241087
  simp only [CollatzResearch.WordTrace]
  refine ⟨8793165277590448226649515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5862110185060298817766343 8793165277590448226649515)
  ·
    refine ⟨13189747916385672339974273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8793165277590448226649515 13189747916385672339974273)
    ·
      refine ⟨9892310937289254254980705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13189747916385672339974273 9892310937289254254980705)
      ·
        refine ⟨7419233202966940691235529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9892310937289254254980705 7419233202966940691235529)
        ·
          refine ⟨5564424902225205518426647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7419233202966940691235529 5564424902225205518426647)
          ·
            refine ⟨8346637353337808277639971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5564424902225205518426647 8346637353337808277639971)
            ·
              refine ⟨12519956030006712416459957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8346637353337808277639971 12519956030006712416459957)
              ·
                refine ⟨1173745877813129289043121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12519956030006712416459957 1173745877813129289043121)
                ·
                  refine ⟨880309408359846966782341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1173745877813129289043121 880309408359846966782341)
                  ·
                    refine ⟨165058014067471306271689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 880309408359846966782341 165058014067471306271689)
                    ·
                      refine ⟨123793510550603479703767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 165058014067471306271689 123793510550603479703767)
                      ·
                        rfl

theorem cell23_241087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 4, 2].length) (baseStart_241087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_241087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_241087 prefixEnd_241087 := by exact prefixLift 241087
  have htrace : WordTrace (prefixWord ++ tailWord_241087) baseStart_241087 baseEnd_241087 := by
    simpa [prefixWord, tailWord_241087, baseEnd_241087] using wordTrace_append hprefix tailTrace_241087
  have hstable : (prefixWord ++ tailWord_241087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241087).length < 2 ^ (prefixWord ++ tailWord_241087).sum := by decide
  have hdescent : baseEnd_241087 < baseStart_241087 := by decide
  rcases family_descends (prefixWord ++ tailWord_241087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241127 : List Nat := [1, 1, 5, 2, 1, 2, 1, 4, 6]
def baseStart_241127 : Nat := 118140960795 + 241127 * 2 ^ 59
def prefixEnd_241127 : Nat := 4983230072969 + 3 ^ 40 * 241127 * 2
def baseEnd_241127 : Nat := 13757116641864813689287

theorem tailTrace_241127 : CollatzResearch.WordTrace tailWord_241127 prefixEnd_241127 13757116641864813689287 := by
  unfold tailWord_241127
  simp only [CollatzResearch.WordTrace]
  refine ⟨8794624197445535058105635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5863082798297023372070423 8794624197445535058105635)
  ·
    refine ⟨13191936296168302587158453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8794624197445535058105635 13191936296168302587158453)
    ·
      refine ⟨1236744027765778367546105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13191936296168302587158453 1236744027765778367546105)
      ·
        refine ⟨927558020824333775659579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1236744027765778367546105 927558020824333775659579)
        ·
          refine ⟨1391337031236500663489369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 927558020824333775659579 1391337031236500663489369)
          ·
            refine ⟨1043502773427375497617027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1391337031236500663489369 1043502773427375497617027)
            ·
              refine ⟨1565254160141063246425541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1043502773427375497617027 1565254160141063246425541)
              ·
                refine ⟨293485155026449358704789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1565254160141063246425541 293485155026449358704789)
                ·
                  refine ⟨13757116641864813689287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 293485155026449358704789 13757116641864813689287)
                  ·
                    rfl

theorem cell23_241127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4, 6].length) (baseStart_241127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_241127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_241127 prefixEnd_241127 := by exact prefixLift 241127
  have htrace : WordTrace (prefixWord ++ tailWord_241127) baseStart_241127 baseEnd_241127 := by
    simpa [prefixWord, tailWord_241127, baseEnd_241127] using wordTrace_append hprefix tailTrace_241127
  have hstable : (prefixWord ++ tailWord_241127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241127).length < 2 ^ (prefixWord ++ tailWord_241127).sum := by decide
  have hdescent : baseEnd_241127 < baseStart_241127 := by decide
  rcases family_descends (prefixWord ++ tailWord_241127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241147 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 3, 5, 2]
def baseStart_241147 : Nat := 118140960795 + 241147 * 2 ^ 59
def prefixEnd_241147 : Nat := 4983230072969 + 3 ^ 40 * 241147 * 2
def baseEnd_241147 : Nat := 123824319389873244953491

theorem tailTrace_241147 : CollatzResearch.WordTrace tailWord_241147 prefixEnd_241147 123824319389873244953491 := by
  unfold tailWord_241147
  simp only [CollatzResearch.WordTrace]
  refine ⟨8795353657373078473833695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5863569104915385649222463 8795353657373078473833695)
  ·
    refine ⟨13193030486059617710750543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8795353657373078473833695 13193030486059617710750543)
    ·
      refine ⟨19789545729089426566125815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13193030486059617710750543 19789545729089426566125815)
      ·
        refine ⟨29684318593634139849188723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19789545729089426566125815 29684318593634139849188723)
        ·
          refine ⟨44526477890451209773783085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29684318593634139849188723 44526477890451209773783085)
          ·
            refine ⟨16697429208919203665168657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44526477890451209773783085 16697429208919203665168657)
            ·
              refine ⟨12523071906689402748876493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16697429208919203665168657 12523071906689402748876493)
              ·
                refine ⟨4696151965008526030828685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12523071906689402748876493 4696151965008526030828685)
                ·
                  refine ⟨1761056986878197261560757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4696151965008526030828685 1761056986878197261560757)
                  ·
                    refine ⟨165099092519830993271321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1761056986878197261560757 165099092519830993271321)
                    ·
                      refine ⟨123824319389873244953491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 165099092519830993271321 123824319389873244953491)
                      ·
                        rfl

theorem cell23_241147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 5, 2].length) (baseStart_241147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_241147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_241147 prefixEnd_241147 := by exact prefixLift 241147
  have htrace : WordTrace (prefixWord ++ tailWord_241147) baseStart_241147 baseEnd_241147 := by
    simpa [prefixWord, tailWord_241147, baseEnd_241147] using wordTrace_append hprefix tailTrace_241147
  have hstable : (prefixWord ++ tailWord_241147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241147).length < 2 ^ (prefixWord ++ tailWord_241147).sum := by decide
  have hdescent : baseEnd_241147 < baseStart_241147 := by decide
  rcases family_descends (prefixWord ++ tailWord_241147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241157 : List Nat := [1, 3, 1, 1, 2, 2, 1, 6, 1, 5]
def baseStart_241157 : Nat := 118140960795 + 241157 * 2 ^ 59
def prefixEnd_241157 : Nat := 4983230072969 + 3 ^ 40 * 241157 * 2
def baseEnd_241157 : Nat := 41276484732139401942815

theorem tailTrace_241157 : CollatzResearch.WordTrace tailWord_241157 prefixEnd_241157 41276484732139401942815 := by
  unfold tailWord_241157
  simp only [CollatzResearch.WordTrace]
  refine ⟨8795718387336850181697725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5863812258224566787798483 8795718387336850181697725)
  ·
    refine ⟨3298394395251318818136647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8795718387336850181697725 3298394395251318818136647)
    ·
      refine ⟨4947591592876978227204971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3298394395251318818136647 4947591592876978227204971)
      ·
        refine ⟨7421387389315467340807457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4947591592876978227204971 7421387389315467340807457)
        ·
          refine ⟨5566040541986600505605593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7421387389315467340807457 5566040541986600505605593)
          ·
            refine ⟨4174530406489950379204195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5566040541986600505605593 4174530406489950379204195)
            ·
              refine ⟨6261795609734925568806293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4174530406489950379204195 6261795609734925568806293)
              ·
                refine ⟨293521669206324636037795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6261795609734925568806293 293521669206324636037795)
                ·
                  refine ⟨440282503809486954056693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 293521669206324636037795 440282503809486954056693)
                  ·
                    refine ⟨41276484732139401942815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 440282503809486954056693 41276484732139401942815)
                    ·
                      rfl

theorem cell23_241157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6, 1, 5].length) (baseStart_241157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_241157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_241157 prefixEnd_241157 := by exact prefixLift 241157
  have htrace : WordTrace (prefixWord ++ tailWord_241157) baseStart_241157 baseEnd_241157 := by
    simpa [prefixWord, tailWord_241157, baseEnd_241157] using wordTrace_append hprefix tailTrace_241157
  have hstable : (prefixWord ++ tailWord_241157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241157).length < 2 ^ (prefixWord ++ tailWord_241157).sum := by decide
  have hdescent : baseEnd_241157 < baseStart_241157 := by decide
  rcases family_descends (prefixWord ++ tailWord_241157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241171 : List Nat := [1, 1, 1, 2, 1, 6, 1, 5, 1, 1, 3]
def baseStart_241171 : Nat := 118140960795 + 241171 * 2 ^ 59
def prefixEnd_241171 : Nat := 4983230072969 + 3 ^ 40 * 241171 * 2
def baseEnd_241171 : Nat := 123836642925581151053381

theorem tailTrace_241171 : CollatzResearch.WordTrace tailWord_241171 prefixEnd_241171 123836642925581151053381 := by
  unfold tailWord_241171
  simp only [CollatzResearch.WordTrace]
  refine ⟨8796229009286130572707367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5864152672857420381804911 8796229009286130572707367)
  ·
    refine ⟨13194343513929195859061051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8796229009286130572707367 13194343513929195859061051)
    ·
      refine ⟨19791515270893793788591577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13194343513929195859061051 19791515270893793788591577)
      ·
        refine ⟨14843636453170345341443683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19791515270893793788591577 14843636453170345341443683)
        ·
          refine ⟨22265454679755518012165525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14843636453170345341443683 22265454679755518012165525)
          ·
            refine ⟨1043693188113539906820259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22265454679755518012165525 1043693188113539906820259)
            ·
              refine ⟨1565539782170309860230389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1043693188113539906820259 1565539782170309860230389)
              ·
                refine ⟨146769354578466549396599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1565539782170309860230389 146769354578466549396599)
                ·
                  refine ⟨220154031867699824094899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146769354578466549396599 220154031867699824094899)
                  ·
                    refine ⟨330231047801549736142349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 220154031867699824094899 330231047801549736142349)
                    ·
                      refine ⟨123836642925581151053381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 330231047801549736142349 123836642925581151053381)
                      ·
                        rfl

theorem cell23_241171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 5, 1, 1, 3].length) (baseStart_241171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_241171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_241171 prefixEnd_241171 := by exact prefixLift 241171
  have htrace : WordTrace (prefixWord ++ tailWord_241171) baseStart_241171 baseEnd_241171 := by
    simpa [prefixWord, tailWord_241171, baseEnd_241171] using wordTrace_append hprefix tailTrace_241171
  have hstable : (prefixWord ++ tailWord_241171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241171).length < 2 ^ (prefixWord ++ tailWord_241171).sum := by decide
  have hdescent : baseEnd_241171 < baseStart_241171 := by decide
  rcases family_descends (prefixWord ++ tailWord_241171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241200 : List Nat := [2, 1, 1, 1, 2, 3, 1, 12]
def baseStart_241200 : Nat := 118140960795 + 241200 * 2 ^ 59
def prefixEnd_241200 : Nat := 4983230072969 + 3 ^ 40 * 241200 * 2
def baseEnd_241200 : Nat := 4587093846835612503361

theorem tailTrace_241200 : CollatzResearch.WordTrace tailWord_241200 prefixEnd_241200 4587093846835612503361 := by
  unfold tailWord_241200
  simp only [CollatzResearch.WordTrace]
  refine ⟨4398643363090534262756527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5864857817454045683675369 4398643363090534262756527)
  ·
    refine ⟨6597965044635801394134791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4398643363090534262756527 6597965044635801394134791)
    ·
      refine ⟨9896947566953702091202187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6597965044635801394134791 9896947566953702091202187)
      ·
        refine ⟨14845421350430553136803281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9896947566953702091202187 14845421350430553136803281)
        ·
          refine ⟨11134066012822914852602461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14845421350430553136803281 11134066012822914852602461)
          ·
            refine ⟨4175274754808593069725923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11134066012822914852602461 4175274754808593069725923)
            ·
              refine ⟨6262912132212889604588885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4175274754808593069725923 6262912132212889604588885)
              ·
                refine ⟨4587093846835612503361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 6262912132212889604588885 4587093846835612503361)
                ·
                  rfl

theorem cell23_241200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 12].length) (baseStart_241200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_241200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_241200 prefixEnd_241200 := by exact prefixLift 241200
  have htrace : WordTrace (prefixWord ++ tailWord_241200) baseStart_241200 baseEnd_241200 := by
    simpa [prefixWord, tailWord_241200, baseEnd_241200] using wordTrace_append hprefix tailTrace_241200
  have hstable : (prefixWord ++ tailWord_241200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241200).length < 2 ^ (prefixWord ++ tailWord_241200).sum := by decide
  have hdescent : baseEnd_241200 < baseStart_241200 := by decide
  rcases family_descends (prefixWord ++ tailWord_241200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241207 : List Nat := [1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 6]
def baseStart_241207 : Nat := 118140960795 + 241207 * 2 ^ 59
def prefixEnd_241207 : Nat := 4983230072969 + 3 ^ 40 * 241207 * 2
def baseEnd_241207 : Nat := 123855128229143010203215

theorem tailTrace_241207 : CollatzResearch.WordTrace tailWord_241207 prefixEnd_241207 123855128229143010203215 := by
  unfold tailWord_241207
  simp only [CollatzResearch.WordTrace]
  refine ⟨8797542037155708721017875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5865028024770472480678583 8797542037155708721017875)
  ·
    refine ⟨13196313055733563081526813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8797542037155708721017875 13196313055733563081526813)
    ·
      refine ⟨4948617395900086155572555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13196313055733563081526813 4948617395900086155572555)
      ·
        refine ⟨7422926093850129233358833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4948617395900086155572555 7422926093850129233358833)
        ·
          refine ⟨5567194570387596925019125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7422926093850129233358833 5567194570387596925019125)
          ·
            refine ⟨521924490973837211720543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5567194570387596925019125 521924490973837211720543)
            ·
              refine ⟨782886736460755817580815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 521924490973837211720543 782886736460755817580815)
              ·
                refine ⟨1174330104691133726371223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 782886736460755817580815 1174330104691133726371223)
                ·
                  refine ⟨1761495157036700589556835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1174330104691133726371223 1761495157036700589556835)
                  ·
                    refine ⟨2642242735555050884335253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1761495157036700589556835 2642242735555050884335253)
                    ·
                      refine ⟨123855128229143010203215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2642242735555050884335253 123855128229143010203215)
                      ·
                        rfl

theorem cell23_241207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 6].length) (baseStart_241207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_241207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_241207 prefixEnd_241207 := by exact prefixLift 241207
  have htrace : WordTrace (prefixWord ++ tailWord_241207) baseStart_241207 baseEnd_241207 := by
    simpa [prefixWord, tailWord_241207, baseEnd_241207] using wordTrace_append hprefix tailTrace_241207
  have hstable : (prefixWord ++ tailWord_241207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241207).length < 2 ^ (prefixWord ++ tailWord_241207).sum := by decide
  have hdescent : baseEnd_241207 < baseStart_241207 := by decide
  rcases family_descends (prefixWord ++ tailWord_241207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241217 : List Nat := [1, 2, 5, 1, 1, 1, 3, 9]
def baseStart_241217 : Nat := 118140960795 + 241217 * 2 ^ 59
def prefixEnd_241217 : Nat := 4983230072969 + 3 ^ 40 * 241217 * 2
def baseEnd_241217 : Nat := 4587417149469924854747

theorem tailTrace_241217 : CollatzResearch.WordTrace tailWord_241217 prefixEnd_241217 4587417149469924854747 := by
  unfold tailWord_241217
  simp only [CollatzResearch.WordTrace]
  refine ⟨8797906767119480428881905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5865271178079653619254603 8797906767119480428881905)
  ·
    refine ⟨6598430075339610321661429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8797906767119480428881905 6598430075339610321661429)
    ·
      refine ⟨618602819563088467655759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6598430075339610321661429 618602819563088467655759)
      ·
        refine ⟨927904229344632701483639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 618602819563088467655759 927904229344632701483639)
        ·
          refine ⟨1391856344016949052225459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 927904229344632701483639 1391856344016949052225459)
          ·
            refine ⟨2087784516025423578338189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1391856344016949052225459 2087784516025423578338189)
            ·
              refine ⟨782919193509533841876821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2087784516025423578338189 782919193509533841876821)
              ·
                refine ⟨4587417149469924854747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 782919193509533841876821 4587417149469924854747)
                ·
                  rfl

theorem cell23_241217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 9].length) (baseStart_241217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_241217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_241217 prefixEnd_241217 := by exact prefixLift 241217
  have htrace : WordTrace (prefixWord ++ tailWord_241217) baseStart_241217 baseEnd_241217 := by
    simpa [prefixWord, tailWord_241217, baseEnd_241217] using wordTrace_append hprefix tailTrace_241217
  have hstable : (prefixWord ++ tailWord_241217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241217).length < 2 ^ (prefixWord ++ tailWord_241217).sum := by decide
  have hdescent : baseEnd_241217 < baseStart_241217 := by decide
  rcases family_descends (prefixWord ++ tailWord_241217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241227 : List Nat := [1, 1, 1, 1, 3, 1, 3, 3, 3, 3, 3]
def baseStart_241227 : Nat := 118140960795 + 241227 * 2 ^ 59
def prefixEnd_241227 : Nat := 4983230072969 + 3 ^ 40 * 241227 * 2
def baseEnd_241227 : Nat := 123865397842232931953123

theorem tailTrace_241227 : CollatzResearch.WordTrace tailWord_241227 prefixEnd_241227 123865397842232931953123 := by
  unfold tailWord_241227
  simp only [CollatzResearch.WordTrace]
  refine ⟨8798271497083252136745935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5865514331388834757830623 8798271497083252136745935)
  ·
    refine ⟨13197407245624878205118903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8798271497083252136745935 13197407245624878205118903)
    ·
      refine ⟨19796110868437317307678355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13197407245624878205118903 19796110868437317307678355)
      ·
        refine ⟨29694166302655975961517533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19796110868437317307678355 29694166302655975961517533)
        ·
          refine ⟨11135312363495990985569075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29694166302655975961517533 11135312363495990985569075)
          ·
            refine ⟨16702968545243986478353613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11135312363495990985569075 16702968545243986478353613)
            ·
              refine ⟨6263613204466494929382605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16702968545243986478353613 6263613204466494929382605)
              ·
                refine ⟨2348854951674935598518477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6263613204466494929382605 2348854951674935598518477)
                ·
                  refine ⟨880820606878100849444429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2348854951674935598518477 880820606878100849444429)
                  ·
                    refine ⟨330307727579287818541661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 880820606878100849444429 330307727579287818541661)
                    ·
                      refine ⟨123865397842232931953123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 330307727579287818541661 123865397842232931953123)
                      ·
                        rfl

theorem cell23_241227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 3, 3].length) (baseStart_241227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_241227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_241227 prefixEnd_241227 := by exact prefixLift 241227
  have htrace : WordTrace (prefixWord ++ tailWord_241227) baseStart_241227 baseEnd_241227 := by
    simpa [prefixWord, tailWord_241227, baseEnd_241227] using wordTrace_append hprefix tailTrace_241227
  have hstable : (prefixWord ++ tailWord_241227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241227).length < 2 ^ (prefixWord ++ tailWord_241227).sum := by decide
  have hdescent : baseEnd_241227 < baseStart_241227 := by decide
  rcases family_descends (prefixWord ++ tailWord_241227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241301 : List Nat := [1, 3, 2, 1, 1, 1, 1, 5, 4, 2, 2]
def baseStart_241301 : Nat := 118140960795 + 241301 * 2 ^ 59
def prefixEnd_241301 : Nat := 4983230072969 + 3 ^ 40 * 241301 * 2
def baseEnd_241301 : Nat := 123903395410665642427783

theorem tailTrace_241301 : CollatzResearch.WordTrace tailWord_241301 prefixEnd_241301 123903395410665642427783 := by
  unfold tailWord_241301
  simp only [CollatzResearch.WordTrace]
  refine ⟨8800970498815162774939757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5867313665876775183293171 8800970498815162774939757)
  ·
    refine ⟨3300363937055686040602409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8800970498815162774939757 3300363937055686040602409)
    ·
      refine ⟨2475272952791764530451807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3300363937055686040602409 2475272952791764530451807)
      ·
        refine ⟨3712909429187646795677711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2475272952791764530451807 3712909429187646795677711)
        ·
          refine ⟨5569364143781470193516567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3712909429187646795677711 5569364143781470193516567)
          ·
            refine ⟨8354046215672205290274851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5569364143781470193516567 8354046215672205290274851)
            ·
              refine ⟨12531069323508307935412277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8354046215672205290274851 12531069323508307935412277)
              ·
                refine ⟨1174787749078903868944901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12531069323508307935412277 1174787749078903868944901)
                ·
                  refine ⟨220272702952294475427169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1174787749078903868944901 220272702952294475427169)
                  ·
                    refine ⟨165204527214220856570377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 220272702952294475427169 165204527214220856570377)
                    ·
                      refine ⟨123903395410665642427783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 165204527214220856570377 123903395410665642427783)
                      ·
                        rfl

theorem cell23_241301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 4, 2, 2].length) (baseStart_241301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_241301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_241301 prefixEnd_241301 := by exact prefixLift 241301
  have htrace : WordTrace (prefixWord ++ tailWord_241301) baseStart_241301 baseEnd_241301 := by
    simpa [prefixWord, tailWord_241301, baseEnd_241301] using wordTrace_append hprefix tailTrace_241301
  have hstable : (prefixWord ++ tailWord_241301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241301).length < 2 ^ (prefixWord ++ tailWord_241301).sum := by decide
  have hdescent : baseEnd_241301 < baseStart_241301 := by decide
  rcases family_descends (prefixWord ++ tailWord_241301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241304 : List Nat := [2, 1, 2, 4, 1, 2, 1, 1, 2, 4, 3]
def baseStart_241304 : Nat := 118140960795 + 241304 * 2 ^ 59
def prefixEnd_241304 : Nat := 4983230072969 + 3 ^ 40 * 241304 * 2
def baseEnd_241304 : Nat := 123904935852629130690269

theorem tailTrace_241304 : CollatzResearch.WordTrace tailWord_241304 prefixEnd_241304 123904935852629130690269 := by
  unfold tailWord_241304
  simp only [CollatzResearch.WordTrace]
  refine ⟨4400539958902147143649483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5867386611869529524865977 4400539958902147143649483)
  ·
    refine ⟨6600809938353220715474225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4400539958902147143649483 6600809938353220715474225)
    ·
      refine ⟨4950607453764915536605669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6600809938353220715474225 4950607453764915536605669)
      ·
        refine ⟨928238897580921663113563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4950607453764915536605669 928238897580921663113563)
        ·
          refine ⟨1392358346371382494670345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 928238897580921663113563 1392358346371382494670345)
          ·
            refine ⟨1044268759778536871002759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1392358346371382494670345 1044268759778536871002759)
            ·
              refine ⟨1566403139667805306504139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1044268759778536871002759 1566403139667805306504139)
              ·
                refine ⟨2349604709501707959756209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1566403139667805306504139 2349604709501707959756209)
                ·
                  refine ⟨1762203532126280969817157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2349604709501707959756209 1762203532126280969817157)
                  ·
                    refine ⟨330413162273677681840717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1762203532126280969817157 330413162273677681840717)
                    ·
                      refine ⟨123904935852629130690269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 330413162273677681840717 123904935852629130690269)
                      ·
                        rfl

theorem cell23_241304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_241304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_241304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_241304 prefixEnd_241304 := by exact prefixLift 241304
  have htrace : WordTrace (prefixWord ++ tailWord_241304) baseStart_241304 baseEnd_241304 := by
    simpa [prefixWord, tailWord_241304, baseEnd_241304] using wordTrace_append hprefix tailTrace_241304
  have hstable : (prefixWord ++ tailWord_241304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241304).length < 2 ^ (prefixWord ++ tailWord_241304).sum := by decide
  have hdescent : baseEnd_241304 < baseStart_241304 := by decide
  rcases family_descends (prefixWord ++ tailWord_241304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241311 : List Nat := [1, 1, 2, 7, 1, 1, 1, 1, 2, 6]
def baseStart_241311 : Nat := 118140960795 + 241311 * 2 ^ 59
def prefixEnd_241311 : Nat := 4983230072969 + 3 ^ 40 * 241311 * 2
def baseEnd_241311 : Nat := 41302843405736867767579

theorem tailTrace_241311 : CollatzResearch.WordTrace tailWord_241311 prefixEnd_241311 41302843405736867767579 := by
  unfold tailWord_241311
  simp only [CollatzResearch.WordTrace]
  refine ⟨8801335228778934482803787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5867556819185956321869191 8801335228778934482803787)
  ·
    refine ⟨13202002843168401724205681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8801335228778934482803787 13202002843168401724205681)
    ·
      refine ⟨9901502132376301293154261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13202002843168401724205681 9901502132376301293154261)
      ·
        refine ⟨232066456227569561558303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 9901502132376301293154261 232066456227569561558303)
        ·
          refine ⟨348099684341354342337455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232066456227569561558303 348099684341354342337455)
          ·
            refine ⟨522149526512031513506183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348099684341354342337455 522149526512031513506183)
            ·
              refine ⟨783224289768047270259275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 522149526512031513506183 783224289768047270259275)
              ·
                refine ⟨1174836434652070905388913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 783224289768047270259275 1174836434652070905388913)
                ·
                  refine ⟨881127325989053179041685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1174836434652070905388913 881127325989053179041685)
                  ·
                    refine ⟨41302843405736867767579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 881127325989053179041685 41302843405736867767579)
                    ·
                      rfl

theorem cell23_241311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 6].length) (baseStart_241311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_241311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_241311 prefixEnd_241311 := by exact prefixLift 241311
  have htrace : WordTrace (prefixWord ++ tailWord_241311) baseStart_241311 baseEnd_241311 := by
    simpa [prefixWord, tailWord_241311, baseEnd_241311] using wordTrace_append hprefix tailTrace_241311
  have hstable : (prefixWord ++ tailWord_241311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241311).length < 2 ^ (prefixWord ++ tailWord_241311).sum := by decide
  have hdescent : baseEnd_241311 < baseStart_241311 := by decide
  rcases family_descends (prefixWord ++ tailWord_241311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241341 : List Nat := [1, 4, 1, 2, 1, 2, 4, 3, 5]
def baseStart_241341 : Nat := 118140960795 + 241341 * 2 ^ 59
def prefixEnd_241341 : Nat := 4983230072969 + 3 ^ 40 * 241341 * 2
def baseEnd_241341 : Nat := 13769326070760609547511

theorem tailTrace_241341 : CollatzResearch.WordTrace tailWord_241341 prefixEnd_241341 13769326070760609547511 := by
  unfold tailWord_241341
  simp only [CollatzResearch.WordTrace]
  refine ⟨8802429418670249606395877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5868286279113499737597251 8802429418670249606395877)
  ·
    refine ⟨1650455516000671801199227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8802429418670249606395877 1650455516000671801199227)
    ·
      refine ⟨2475683274001007701798841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1650455516000671801199227 2475683274001007701798841)
      ·
        refine ⟨1856762455500755776349131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2475683274001007701798841 1856762455500755776349131)
        ·
          refine ⟨2785143683251133664523697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1856762455500755776349131 2785143683251133664523697)
          ·
            refine ⟨2088857762438350248392773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2785143683251133664523697 2088857762438350248392773)
            ·
              refine ⟨391660830457190671573645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2088857762438350248392773 391660830457190671573645)
              ·
                refine ⟨146872811421446501840117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 391660830457190671573645 146872811421446501840117)
                ·
                  refine ⟨13769326070760609547511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 146872811421446501840117 13769326070760609547511)
                  ·
                    rfl

theorem cell23_241341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 3, 5].length) (baseStart_241341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_241341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_241341 prefixEnd_241341 := by exact prefixLift 241341
  have htrace : WordTrace (prefixWord ++ tailWord_241341) baseStart_241341 baseEnd_241341 := by
    simpa [prefixWord, tailWord_241341, baseEnd_241341] using wordTrace_append hprefix tailTrace_241341
  have hstable : (prefixWord ++ tailWord_241341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241341).length < 2 ^ (prefixWord ++ tailWord_241341).sum := by decide
  have hdescent : baseEnd_241341 < baseStart_241341 := by decide
  rcases family_descends (prefixWord ++ tailWord_241341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241346 : List Nat := [3, 5, 1, 2, 2, 1, 1, 2, 2, 1, 3]
def baseStart_241346 : Nat := 118140960795 + 241346 * 2 ^ 59
def prefixEnd_241346 : Nat := 4983230072969 + 3 ^ 40 * 241346 * 2
def baseEnd_241346 : Nat := 123926502040117966365077

theorem tailTrace_241346 : CollatzResearch.WordTrace tailWord_241346 prefixEnd_241346 123926502040117966365077 := by
  unfold tailWord_241346
  simp only [CollatzResearch.WordTrace]
  refine ⟨2200652945913033865081973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5868407855768090306885261 2200652945913033865081973)
  ·
    refine ⟨206311213679346924851435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2200652945913033865081973 206311213679346924851435)
    ·
      refine ⟨309466820519020387277153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206311213679346924851435 309466820519020387277153)
      ·
        refine ⟨232100115389265290457865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309466820519020387277153 232100115389265290457865)
        ·
          refine ⟨174075086541948967843399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232100115389265290457865 174075086541948967843399)
          ·
            refine ⟨261112629812923451765099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174075086541948967843399 261112629812923451765099)
            ·
              refine ⟨391668944719385177647649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261112629812923451765099 391668944719385177647649)
              ·
                refine ⟨293751708539538883235737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 391668944719385177647649 293751708539538883235737)
                ·
                  refine ⟨220313781404654162426803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 293751708539538883235737 220313781404654162426803)
                  ·
                    refine ⟨330470672106981243640205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 220313781404654162426803 330470672106981243640205)
                    ·
                      refine ⟨123926502040117966365077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 330470672106981243640205 123926502040117966365077)
                      ·
                        rfl

theorem cell23_241346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_241346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_241346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_241346 prefixEnd_241346 := by exact prefixLift 241346
  have htrace : WordTrace (prefixWord ++ tailWord_241346) baseStart_241346 baseEnd_241346 := by
    simpa [prefixWord, tailWord_241346, baseEnd_241346] using wordTrace_append hprefix tailTrace_241346
  have hstable : (prefixWord ++ tailWord_241346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241346).length < 2 ^ (prefixWord ++ tailWord_241346).sum := by decide
  have hdescent : baseEnd_241346 < baseStart_241346 := by decide
  rcases family_descends (prefixWord ++ tailWord_241346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241418 : List Nat := [3, 1, 2, 2, 1, 5, 1, 1, 3, 4]
def baseStart_241418 : Nat := 118140960795 + 241418 * 2 ^ 59
def prefixEnd_241418 : Nat := 4983230072969 + 3 ^ 40 * 241418 * 2
def baseEnd_241418 : Nat := 41321157549080561554915

theorem tailTrace_241418 : CollatzResearch.WordTrace tailWord_241418 prefixEnd_241418 41321157549080561554915 := by
  unfold tailWord_241418
  simp only [CollatzResearch.WordTrace]
  refine ⟨2201309459847822939237227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5870158559594194504632605 2201309459847822939237227)
  ·
    refine ⟨3301964189771734408855841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2201309459847822939237227 3301964189771734408855841)
    ·
      refine ⟨2476473142328800806641881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3301964189771734408855841 2476473142328800806641881)
      ·
        refine ⟨1857354856746600604981411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2476473142328800806641881 1857354856746600604981411)
        ·
          refine ⟨2786032285119900907472117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1857354856746600604981411 2786032285119900907472117)
          ·
            refine ⟨261190526729990710075511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2786032285119900907472117 261190526729990710075511)
            ·
              refine ⟨391785790094986065113267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261190526729990710075511 391785790094986065113267)
              ·
                refine ⟨587678685142479097669901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 391785790094986065113267 587678685142479097669901)
                ·
                  refine ⟨220379506928429661626213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 587678685142479097669901 220379506928429661626213)
                  ·
                    refine ⟨41321157549080561554915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 220379506928429661626213 41321157549080561554915)
                    ·
                      rfl

theorem cell23_241418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 3, 4].length) (baseStart_241418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_241418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_241418 prefixEnd_241418 := by exact prefixLift 241418
  have htrace : WordTrace (prefixWord ++ tailWord_241418) baseStart_241418 baseEnd_241418 := by
    simpa [prefixWord, tailWord_241418, baseEnd_241418] using wordTrace_append hprefix tailTrace_241418
  have hstable : (prefixWord ++ tailWord_241418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241418).length < 2 ^ (prefixWord ++ tailWord_241418).sum := by decide
  have hdescent : baseEnd_241418 < baseStart_241418 := by decide
  rcases family_descends (prefixWord ++ tailWord_241418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241431 : List Nat := [1, 1, 3, 4, 2, 2, 1, 3, 6]
def baseStart_241431 : Nat := 118140960795 + 241431 * 2 ^ 59
def prefixEnd_241431 : Nat := 4983230072969 + 3 ^ 40 * 241431 * 2
def baseEnd_241431 : Nat := 13774460877305570422465

theorem tailTrace_241431 : CollatzResearch.WordTrace tailWord_241431 prefixEnd_241431 13774460877305570422465 := by
  unfold tailWord_241431
  simp only [CollatzResearch.WordTrace]
  refine ⟨8805711988344194977172147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5870474658896129984781431 8805711988344194977172147)
  ·
    refine ⟨13208567982516292465758221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8805711988344194977172147 13208567982516292465758221)
    ·
      refine ⟨4953212993443609674659333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13208567982516292465758221 4953212993443609674659333)
      ·
        refine ⟨928727436270676813998625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4953212993443609674659333 928727436270676813998625)
        ·
          refine ⟨696545577203007610498969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 928727436270676813998625 696545577203007610498969)
          ·
            refine ⟨522409182902255707874227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 696545577203007610498969 522409182902255707874227)
            ·
              refine ⟨783613774353383561811341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 522409182902255707874227 783613774353383561811341)
              ·
                refine ⟨293855165382518835679253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 783613774353383561811341 293855165382518835679253)
                ·
                  refine ⟨13774460877305570422465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 293855165382518835679253 13774460877305570422465)
                  ·
                    rfl

theorem cell23_241431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3, 6].length) (baseStart_241431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_241431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_241431 prefixEnd_241431 := by exact prefixLift 241431
  have htrace : WordTrace (prefixWord ++ tailWord_241431) baseStart_241431 baseEnd_241431 := by
    simpa [prefixWord, tailWord_241431, baseEnd_241431] using wordTrace_append hprefix tailTrace_241431
  have hstable : (prefixWord ++ tailWord_241431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241431).length < 2 ^ (prefixWord ++ tailWord_241431).sum := by decide
  have hdescent : baseEnd_241431 < baseStart_241431 := by decide
  rcases family_descends (prefixWord ++ tailWord_241431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241468 : List Nat := [2, 2, 2, 2, 1, 1, 4, 2, 2, 3, 2]
def baseStart_241468 : Nat := 118140960795 + 241468 * 2 ^ 59
def prefixEnd_241468 : Nat := 4983230072969 + 3 ^ 40 * 241468 * 2
def baseEnd_241468 : Nat := 123989146679966489039515

theorem tailTrace_241468 : CollatzResearch.WordTrace tailWord_241468 prefixEnd_241468 123989146679966489039515 := by
  unfold tailWord_241468
  simp only [CollatzResearch.WordTrace]
  refine ⟨4403530744605075148134529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5871374326140100197512705 4403530744605075148134529)
  ·
    refine ⟨3302648058453806361100897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4403530744605075148134529 3302648058453806361100897)
    ·
      refine ⟨2476986043840354770825673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3302648058453806361100897 2476986043840354770825673)
      ·
        refine ⟨1857739532880266078119255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2476986043840354770825673 1857739532880266078119255)
        ·
          refine ⟨2786609299320399117178883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1857739532880266078119255 2786609299320399117178883)
          ·
            refine ⟨4179913948980598675768325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2786609299320399117178883 4179913948980598675768325)
            ·
              refine ⟨783733865433862251706561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4179913948980598675768325 783733865433862251706561)
              ·
                refine ⟨587800399075396688779921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 783733865433862251706561 587800399075396688779921)
                ·
                  refine ⟨440850299306547516584941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 587800399075396688779921 440850299306547516584941)
                  ·
                    refine ⟨165318862239955318719353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 440850299306547516584941 165318862239955318719353)
                    ·
                      refine ⟨123989146679966489039515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 165318862239955318719353 123989146679966489039515)
                      ·
                        rfl

theorem cell23_241468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 2, 3, 2].length) (baseStart_241468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_241468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_241468 prefixEnd_241468 := by exact prefixLift 241468
  have htrace : WordTrace (prefixWord ++ tailWord_241468) baseStart_241468 baseEnd_241468 := by
    simpa [prefixWord, tailWord_241468, baseEnd_241468] using wordTrace_append hprefix tailTrace_241468
  have hstable : (prefixWord ++ tailWord_241468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241468).length < 2 ^ (prefixWord ++ tailWord_241468).sum := by decide
  have hdescent : baseEnd_241468 < baseStart_241468 := by decide
  rcases family_descends (prefixWord ++ tailWord_241468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241475 : List Nat := [1, 1, 1, 3, 1, 6, 1, 4, 1, 1, 3]
def baseStart_241475 : Nat := 118140960795 + 241475 * 2 ^ 59
def prefixEnd_241475 : Nat := 4983230072969 + 3 ^ 40 * 241475 * 2
def baseEnd_241475 : Nat := 123992741044547961651983

theorem tailTrace_241475 : CollatzResearch.WordTrace tailWord_241475 prefixEnd_241475 123992741044547961651983 := by
  unfold tailWord_241475
  simp only [CollatzResearch.WordTrace]
  refine ⟨8807316800184790491773879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5871544533456526994515919 8807316800184790491773879)
  ·
    refine ⟨13210975200277185737660819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8807316800184790491773879 13210975200277185737660819)
    ·
      refine ⟨19816462800415778606491229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13210975200277185737660819 19816462800415778606491229)
      ·
        refine ⟨7431173550155916977434211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19816462800415778606491229 7431173550155916977434211)
        ·
          refine ⟨11146760325233875466151317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7431173550155916977434211 11146760325233875466151317)
          ·
            refine ⟨522504390245337912475843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11146760325233875466151317 522504390245337912475843)
            ·
              refine ⟨783756585368006868713765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 522504390245337912475843 783756585368006868713765)
              ·
                refine ⟨146954359756501287883831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 783756585368006868713765 146954359756501287883831)
                ·
                  refine ⟨220431539634751931825747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146954359756501287883831 220431539634751931825747)
                  ·
                    refine ⟨330647309452127897738621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 220431539634751931825747 330647309452127897738621)
                    ·
                      refine ⟨123992741044547961651983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 330647309452127897738621 123992741044547961651983)
                      ·
                        rfl

theorem cell23_241475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 4, 1, 1, 3].length) (baseStart_241475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_241475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_241475 prefixEnd_241475 := by exact prefixLift 241475
  have htrace : WordTrace (prefixWord ++ tailWord_241475) baseStart_241475 baseEnd_241475 := by
    simpa [prefixWord, tailWord_241475, baseEnd_241475] using wordTrace_append hprefix tailTrace_241475
  have hstable : (prefixWord ++ tailWord_241475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241475).length < 2 ^ (prefixWord ++ tailWord_241475).sum := by decide
  have hdescent : baseEnd_241475 < baseStart_241475 := by decide
  rcases family_descends (prefixWord ++ tailWord_241475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241511 : List Nat := [1, 1, 5, 1, 2, 1, 1, 4, 1, 2, 4]
def baseStart_241511 : Nat := 118140960795 + 241511 * 2 ^ 59
def prefixEnd_241511 : Nat := 4983230072969 + 3 ^ 40 * 241511 * 2
def baseEnd_241511 : Nat := 124011226348109820801817

theorem tailTrace_241511 : CollatzResearch.WordTrace tailWord_241511 prefixEnd_241511 124011226348109820801817 := by
  unfold tailWord_241511
  simp only [CollatzResearch.WordTrace]
  refine ⟨8808629828054368640084387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5872419885369579093389591 8808629828054368640084387)
  ·
    refine ⟨13212944742081552960126581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8808629828054368640084387 13212944742081552960126581)
    ·
      refine ⟨1238713569570145590011867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13212944742081552960126581 1238713569570145590011867)
      ·
        refine ⟨1858070354355218385017801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1238713569570145590011867 1858070354355218385017801)
        ·
          refine ⟨1393552765766413788763351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1858070354355218385017801 1393552765766413788763351)
          ·
            refine ⟨2090329148649620683145027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1393552765766413788763351 2090329148649620683145027)
            ·
              refine ⟨3135493722974431024717541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2090329148649620683145027 3135493722974431024717541)
              ·
                refine ⟨587905073057705817134539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3135493722974431024717541 587905073057705817134539)
                ·
                  refine ⟨881857609586558725701809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 587905073057705817134539 881857609586558725701809)
                  ·
                    refine ⟨661393207189919044276357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 881857609586558725701809 661393207189919044276357)
                    ·
                      refine ⟨124011226348109820801817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 661393207189919044276357 124011226348109820801817)
                      ·
                        rfl

theorem cell23_241511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_241511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_241511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_241511 prefixEnd_241511 := by exact prefixLift 241511
  have htrace : WordTrace (prefixWord ++ tailWord_241511) baseStart_241511 baseEnd_241511 := by
    simpa [prefixWord, tailWord_241511, baseEnd_241511] using wordTrace_append hprefix tailTrace_241511
  have hstable : (prefixWord ++ tailWord_241511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241511).length < 2 ^ (prefixWord ++ tailWord_241511).sum := by decide
  have hdescent : baseEnd_241511 < baseStart_241511 := by decide
  rcases family_descends (prefixWord ++ tailWord_241511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241591 : List Nat := [1, 1, 3, 1, 3, 1, 1, 3, 2, 4, 3]
def baseStart_241591 : Nat := 118140960795 + 241591 * 2 ^ 59
def prefixEnd_241591 : Nat := 4983230072969 + 3 ^ 40 * 241591 * 2
def baseEnd_241591 : Nat := 124052304800469507801449

theorem tailTrace_241591 : CollatzResearch.WordTrace tailWord_241591 prefixEnd_241591 124052304800469507801449 := by
  unfold tailWord_241591
  simp only [CollatzResearch.WordTrace]
  refine ⟨8811547667764542302996627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5874365111843028201997751 8811547667764542302996627)
  ·
    refine ⟨13217321501646813454494941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8811547667764542302996627 13217321501646813454494941)
    ·
      refine ⟨4956495563117555045435603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13217321501646813454494941 4956495563117555045435603)
      ·
        refine ⟨7434743344676332568153405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4956495563117555045435603 7434743344676332568153405)
        ·
          refine ⟨2788028754253624713057527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7434743344676332568153405 2788028754253624713057527)
          ·
            refine ⟨4182043131380437069586291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2788028754253624713057527 4182043131380437069586291)
            ·
              refine ⟨6273064697070655604379437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4182043131380437069586291 6273064697070655604379437)
              ·
                refine ⟨2352399261401495851642289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6273064697070655604379437 2352399261401495851642289)
                ·
                  refine ⟨1764299446051121888731717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2352399261401495851642289 1764299446051121888731717)
                  ·
                    refine ⟨330806146134585354137197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1764299446051121888731717 330806146134585354137197)
                    ·
                      refine ⟨124052304800469507801449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 330806146134585354137197 124052304800469507801449)
                      ·
                        rfl

theorem cell23_241591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 4, 3].length) (baseStart_241591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_241591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_241591 prefixEnd_241591 := by exact prefixLift 241591
  have htrace : WordTrace (prefixWord ++ tailWord_241591) baseStart_241591 baseEnd_241591 := by
    simpa [prefixWord, tailWord_241591, baseEnd_241591] using wordTrace_append hprefix tailTrace_241591
  have hstable : (prefixWord ++ tailWord_241591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241591).length < 2 ^ (prefixWord ++ tailWord_241591).sum := by decide
  have hdescent : baseEnd_241591 < baseStart_241591 := by decide
  rcases family_descends (prefixWord ++ tailWord_241591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241639 : List Nat := [1, 1, 5, 2, 3, 1, 2, 2, 2, 2, 2]
def baseStart_241639 : Nat := 118140960795 + 241639 * 2 ^ 59
def prefixEnd_241639 : Nat := 4983230072969 + 3 ^ 40 * 241639 * 2
def baseEnd_241639 : Nat := 124076951871885320001229

theorem tailTrace_241639 : CollatzResearch.WordTrace tailWord_241639 prefixEnd_241639 124076951871885320001229 := by
  unfold tailWord_241639
  simp only [CollatzResearch.WordTrace]
  refine ⟨8813298371590646500743971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5875532247727097667162647 8813298371590646500743971)
  ·
    refine ⟨13219947557385969751115957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8813298371590646500743971 13219947557385969751115957)
    ·
      refine ⟨1239370083504934664167121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13219947557385969751115957 1239370083504934664167121)
      ·
        refine ⟨929527562628700998125341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1239370083504934664167121 929527562628700998125341)
        ·
          refine ⟨348572835985762874297003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 929527562628700998125341 348572835985762874297003)
          ·
            refine ⟨522859253978644311445505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348572835985762874297003 522859253978644311445505)
            ·
              refine ⟨392144440483983233584129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 522859253978644311445505 392144440483983233584129)
              ·
                refine ⟨294108330362987425188097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 392144440483983233584129 294108330362987425188097)
                ·
                  refine ⟨220581247772240568891073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 294108330362987425188097 220581247772240568891073)
                  ·
                    refine ⟨165435935829180426668305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 220581247772240568891073 165435935829180426668305)
                    ·
                      refine ⟨124076951871885320001229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 165435935829180426668305 124076951871885320001229)
                      ·
                        rfl

theorem cell23_241639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_241639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_241639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_241639 prefixEnd_241639 := by exact prefixLift 241639
  have htrace : WordTrace (prefixWord ++ tailWord_241639) baseStart_241639 baseEnd_241639 := by
    simpa [prefixWord, tailWord_241639, baseEnd_241639] using wordTrace_append hprefix tailTrace_241639
  have hstable : (prefixWord ++ tailWord_241639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241639).length < 2 ^ (prefixWord ++ tailWord_241639).sum := by decide
  have hdescent : baseEnd_241639 < baseStart_241639 := by decide
  rcases family_descends (prefixWord ++ tailWord_241639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241648 : List Nat := [2, 1, 1, 1, 3, 2, 3, 1, 2, 5, 2]
def baseStart_241648 : Nat := 118140960795 + 241648 * 2 ^ 59
def prefixEnd_241648 : Nat := 4983230072969 + 3 ^ 40 * 241648 * 2
def baseEnd_241648 : Nat := 124081573197775784788687

theorem tailTrace_241648 : CollatzResearch.WordTrace tailWord_241648 prefixEnd_241648 124081573197775784788687 := by
  unfold tailWord_241648
  simp only [CollatzResearch.WordTrace]
  refine ⟨4406813314279020518910799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5875751085705360691881065 4406813314279020518910799)
  ·
    refine ⟨6610219971418530778366199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4406813314279020518910799 6610219971418530778366199)
    ·
      refine ⟨9915329957127796167549299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6610219971418530778366199 9915329957127796167549299)
      ·
        refine ⟨14872994935691694251323949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9915329957127796167549299 14872994935691694251323949)
        ·
          refine ⟨5577373100884385344246481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14872994935691694251323949 5577373100884385344246481)
          ·
            refine ⟨4183029825663289008184861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5577373100884385344246481 4183029825663289008184861)
            ·
              refine ⟨1568636184623733378069323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4183029825663289008184861 1568636184623733378069323)
              ·
                refine ⟨2352954276935600067103985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1568636184623733378069323 2352954276935600067103985)
                ·
                  refine ⟨1764715707701700050327989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2352954276935600067103985 1764715707701700050327989)
                  ·
                    refine ⟨165442097597034379718249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1764715707701700050327989 165442097597034379718249)
                    ·
                      refine ⟨124081573197775784788687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 165442097597034379718249 124081573197775784788687)
                      ·
                        rfl

theorem cell23_241648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 2, 5, 2].length) (baseStart_241648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_241648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_241648 prefixEnd_241648 := by exact prefixLift 241648
  have htrace : WordTrace (prefixWord ++ tailWord_241648) baseStart_241648 baseEnd_241648 := by
    simpa [prefixWord, tailWord_241648, baseEnd_241648] using wordTrace_append hprefix tailTrace_241648
  have hstable : (prefixWord ++ tailWord_241648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241648).length < 2 ^ (prefixWord ++ tailWord_241648).sum := by decide
  have hdescent : baseEnd_241648 < baseStart_241648 := by decide
  rcases family_descends (prefixWord ++ tailWord_241648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241678 : List Nat := [4, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4]
def baseStart_241678 : Nat := 118140960795 + 241678 * 2 ^ 59
def prefixEnd_241678 : Nat := 4983230072969 + 3 ^ 40 * 241678 * 2
def baseEnd_241678 : Nat := 124096977617410667413549

theorem tailTrace_241678 : CollatzResearch.WordTrace tailWord_241678 prefixEnd_241678 124096977617410667413549 := by
  unfold tailWord_241678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1101840102306169520176711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5876480545632904107609125 1101840102306169520176711)
  ·
    refine ⟨1652760153459254280265067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1101840102306169520176711 1652760153459254280265067)
    ·
      refine ⟨2479140230188881420397601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1652760153459254280265067 2479140230188881420397601)
      ·
        refine ⟨1859355172641661065298201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2479140230188881420397601 1859355172641661065298201)
        ·
          refine ⟨1394516379481245798973651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1859355172641661065298201 1394516379481245798973651)
          ·
            refine ⟨2091774569221868698460477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1394516379481245798973651 2091774569221868698460477)
            ·
              refine ⟨784415463458200761922679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2091774569221868698460477 784415463458200761922679)
              ·
                refine ⟨1176623195187301142884019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 784415463458200761922679 1176623195187301142884019)
                ·
                  refine ⟨1764934792780951714326029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1176623195187301142884019 1764934792780951714326029)
                  ·
                    refine ⟨661850547292856892872261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1764934792780951714326029 661850547292856892872261)
                    ·
                      refine ⟨124096977617410667413549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 661850547292856892872261 124096977617410667413549)
                      ·
                        rfl

theorem cell23_241678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_241678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_241678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_241678 prefixEnd_241678 := by exact prefixLift 241678
  have htrace : WordTrace (prefixWord ++ tailWord_241678) baseStart_241678 baseEnd_241678 := by
    simpa [prefixWord, tailWord_241678, baseEnd_241678] using wordTrace_append hprefix tailTrace_241678
  have hstable : (prefixWord ++ tailWord_241678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241678).length < 2 ^ (prefixWord ++ tailWord_241678).sum := by decide
  have hdescent : baseEnd_241678 < baseStart_241678 := by decide
  rcases family_descends (prefixWord ++ tailWord_241678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241688 : List Nat := [2, 1, 2, 3, 2, 1, 1, 2, 5, 4]
def baseStart_241688 : Nat := 118140960795 + 241688 * 2 ^ 59
def prefixEnd_241688 : Nat := 4983230072969 + 3 ^ 40 * 241688 * 2
def baseEnd_241688 : Nat := 41367370807985209429501

theorem tailTrace_241688 : CollatzResearch.WordTrace tailWord_241688 prefixEnd_241688 41367370807985209429501 := by
  unfold tailWord_241688
  simp only [CollatzResearch.WordTrace]
  refine ⟨4407542774206563934638859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5876723698942085246185145 4407542774206563934638859)
  ·
    refine ⟨6611314161309845901958289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4407542774206563934638859 6611314161309845901958289)
    ·
      refine ⟨4958485620982384426468717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6611314161309845901958289 4958485620982384426468717)
      ·
        refine ⟨1859432107868394159925769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4958485620982384426468717 1859432107868394159925769)
        ·
          refine ⟨1394574080901295619944327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1859432107868394159925769 1394574080901295619944327)
          ·
            refine ⟨2091861121351943429916491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1394574080901295619944327 2091861121351943429916491)
            ·
              refine ⟨3137791682027915144874737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2091861121351943429916491 3137791682027915144874737)
              ·
                refine ⟨2353343761520936358656053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3137791682027915144874737 2353343761520936358656053)
                ·
                  refine ⟨220625977642587783624005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2353343761520936358656053 220625977642587783624005)
                  ·
                    refine ⟨41367370807985209429501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 220625977642587783624005 41367370807985209429501)
                    ·
                      rfl

theorem cell23_241688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 5, 4].length) (baseStart_241688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_241688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_241688 prefixEnd_241688 := by exact prefixLift 241688
  have htrace : WordTrace (prefixWord ++ tailWord_241688) baseStart_241688 baseEnd_241688 := by
    simpa [prefixWord, tailWord_241688, baseEnd_241688] using wordTrace_append hprefix tailTrace_241688
  have hstable : (prefixWord ++ tailWord_241688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241688).length < 2 ^ (prefixWord ++ tailWord_241688).sum := by decide
  have hdescent : baseEnd_241688 < baseStart_241688 := by decide
  rcases family_descends (prefixWord ++ tailWord_241688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241748 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 5, 5]
def baseStart_241748 : Nat := 118140960795 + 241748 * 2 ^ 59
def prefixEnd_241748 : Nat := 4983230072969 + 3 ^ 40 * 241748 * 2
def baseEnd_241748 : Nat := 41377640421075131179409

theorem tailTrace_241748 : CollatzResearch.WordTrace tailWord_241748 prefixEnd_241748 41377640421075131179409 := by
  unfold tailWord_241748
  simp only [CollatzResearch.WordTrace]
  refine ⟨4408636964097879058230949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5878182618797172077641265 4408636964097879058230949)
  ·
    refine ⟨826619430768352323418303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4408636964097879058230949 826619430768352323418303)
    ·
      refine ⟨1239929146152528485127455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 826619430768352323418303 1239929146152528485127455)
      ·
        refine ⟨1859893719228792727691183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1239929146152528485127455 1859893719228792727691183)
        ·
          refine ⟨2789840578843189091536775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1859893719228792727691183 2789840578843189091536775)
          ·
            refine ⟨4184760868264783637305163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2789840578843189091536775 4184760868264783637305163)
            ·
              refine ⟨6277141302397175455957745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4184760868264783637305163 6277141302397175455957745)
              ·
                refine ⟨4707855976797881591968309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6277141302397175455957745 4707855976797881591968309)
                ·
                  refine ⟨441361497824801399247029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4707855976797881591968309 441361497824801399247029)
                  ·
                    refine ⟨41377640421075131179409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 441361497824801399247029 41377640421075131179409)
                    ·
                      rfl

theorem cell23_241748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_241748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_241748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_241748 prefixEnd_241748 := by exact prefixLift 241748
  have htrace : WordTrace (prefixWord ++ tailWord_241748) baseStart_241748 baseEnd_241748 := by
    simpa [prefixWord, tailWord_241748, baseEnd_241748] using wordTrace_append hprefix tailTrace_241748
  have hstable : (prefixWord ++ tailWord_241748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241748).length < 2 ^ (prefixWord ++ tailWord_241748).sum := by decide
  have hdescent : baseEnd_241748 < baseStart_241748 := by decide
  rcases family_descends (prefixWord ++ tailWord_241748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241782 : List Nat := [5, 1, 1, 2, 1, 2, 3, 2, 1, 5]
def baseStart_241782 : Nat := 118140960795 + 241782 * 2 ^ 59
def prefixEnd_241782 : Nat := 4983230072969 + 3 ^ 40 * 241782 * 2
def baseEnd_241782 : Nat := 41383459868492753504357

theorem tailTrace_241782 : CollatzResearch.WordTrace tailWord_241782 prefixEnd_241782 41383459868492753504357 := by
  unfold tailWord_241782
  simp only [CollatzResearch.WordTrace]
  refine ⟨551157125629536370199975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5879009340048387948799733 551157125629536370199975)
  ·
    refine ⟨826735688444304555299963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 551157125629536370199975 826735688444304555299963)
    ·
      refine ⟨1240103532666456832949945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 826735688444304555299963 1240103532666456832949945)
      ·
        refine ⟨930077649499842624712459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1240103532666456832949945 930077649499842624712459)
        ·
          refine ⟨1395116474249763937068689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 930077649499842624712459 1395116474249763937068689)
          ·
            refine ⟨1046337355687322952801517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1395116474249763937068689 1046337355687322952801517)
            ·
              refine ⟨392376508382746107300569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1046337355687322952801517 392376508382746107300569)
              ·
                refine ⟨294282381287059580475427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 392376508382746107300569 294282381287059580475427)
                ·
                  refine ⟨441423571930589370713141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 294282381287059580475427 441423571930589370713141)
                  ·
                    refine ⟨41383459868492753504357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 441423571930589370713141 41383459868492753504357)
                    ·
                      rfl

theorem cell23_241782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_241782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_241782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_241782 prefixEnd_241782 := by exact prefixLift 241782
  have htrace : WordTrace (prefixWord ++ tailWord_241782) baseStart_241782 baseEnd_241782 := by
    simpa [prefixWord, tailWord_241782, baseEnd_241782] using wordTrace_append hprefix tailTrace_241782
  have hstable : (prefixWord ++ tailWord_241782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241782).length < 2 ^ (prefixWord ++ tailWord_241782).sum := by decide
  have hdescent : baseEnd_241782 < baseStart_241782 := by decide
  rcases family_descends (prefixWord ++ tailWord_241782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241785 : List Nat := [1, 2, 1, 3, 4, 2, 1, 1, 3, 1, 4]
def baseStart_241785 : Nat := 118140960795 + 241785 * 2 ^ 59
def prefixEnd_241785 : Nat := 4983230072969 + 3 ^ 40 * 241785 * 2
def baseEnd_241785 : Nat := 124151920047441748775557

theorem tailTrace_241785 : CollatzResearch.WordTrace tailWord_241785 prefixEnd_241785 124151920047441748775557 := by
  unfold tailWord_241785
  simp only [CollatzResearch.WordTrace]
  refine ⟨8818623429061713435558809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5879082286041142290372539 8818623429061713435558809)
  ·
    refine ⟨6613967571796285076669107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8818623429061713435558809 6613967571796285076669107)
    ·
      refine ⟨9920951357694427615003661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6613967571796285076669107 9920951357694427615003661)
      ·
        refine ⟨3720356759135410355626373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9920951357694427615003661 3720356759135410355626373)
        ·
          refine ⟨697566892337889441679945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3720356759135410355626373 697566892337889441679945)
          ·
            refine ⟨523175169253417081259959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 697566892337889441679945 523175169253417081259959)
            ·
              refine ⟨784762753880125621889939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523175169253417081259959 784762753880125621889939)
              ·
                refine ⟨1177144130820188432834909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 784762753880125621889939 1177144130820188432834909)
                ·
                  refine ⟨441429049057570662313091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1177144130820188432834909 441429049057570662313091)
                  ·
                    refine ⟨662143573586355993469637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 441429049057570662313091 662143573586355993469637)
                    ·
                      refine ⟨124151920047441748775557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 662143573586355993469637 124151920047441748775557)
                      ·
                        rfl

theorem cell23_241785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_241785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_241785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_241785 prefixEnd_241785 := by exact prefixLift 241785
  have htrace : WordTrace (prefixWord ++ tailWord_241785) baseStart_241785 baseEnd_241785 := by
    simpa [prefixWord, tailWord_241785, baseEnd_241785] using wordTrace_append hprefix tailTrace_241785
  have hstable : (prefixWord ++ tailWord_241785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241785).length < 2 ^ (prefixWord ++ tailWord_241785).sum := by decide
  have hdescent : baseEnd_241785 < baseStart_241785 := by decide
  rcases family_descends (prefixWord ++ tailWord_241785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241825 : List Nat := [1, 2, 3, 3, 1, 4, 1, 8]
def baseStart_241825 : Nat := 118140960795 + 241825 * 2 ^ 59
def prefixEnd_241825 : Nat := 4983230072969 + 3 ^ 40 * 241825 * 2
def baseEnd_241825 : Nat := 4598979973097096010199

theorem tailTrace_241825 : CollatzResearch.WordTrace tailWord_241825 prefixEnd_241825 4598979973097096010199 := by
  unfold tailWord_241825
  simp only [CollatzResearch.WordTrace]
  refine ⟨8820082348916800267014929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5880054899277866844676619 8820082348916800267014929)
  ·
    refine ⟨6615061761687600200261197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8820082348916800267014929 6615061761687600200261197)
    ·
      refine ⟨2480648160632850075097949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6615061761687600200261197 2480648160632850075097949)
      ·
        refine ⟨930243060237318778161731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2480648160632850075097949 930243060237318778161731)
        ·
          refine ⟨1395364590355978167242597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 930243060237318778161731 1395364590355978167242597)
          ·
            refine ⟨261630860691745906357987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1395364590355978167242597 261630860691745906357987)
            ·
              refine ⟨392446291037618859536981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261630860691745906357987 392446291037618859536981)
              ·
                refine ⟨4598979973097096010199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 392446291037618859536981 4598979973097096010199)
                ·
                  rfl

theorem cell23_241825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 8].length) (baseStart_241825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_241825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_241825 prefixEnd_241825 := by exact prefixLift 241825
  have htrace : WordTrace (prefixWord ++ tailWord_241825) baseStart_241825 baseEnd_241825 := by
    simpa [prefixWord, tailWord_241825, baseEnd_241825] using wordTrace_append hprefix tailTrace_241825
  have hstable : (prefixWord ++ tailWord_241825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241825).length < 2 ^ (prefixWord ++ tailWord_241825).sum := by decide
  have hdescent : baseEnd_241825 < baseStart_241825 := by decide
  rcases family_descends (prefixWord ++ tailWord_241825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241848 : List Nat := [2, 1, 2, 1, 2, 1, 4, 1, 2, 2, 5]
def baseStart_241848 : Nat := 118140960795 + 241848 * 2 ^ 59
def prefixEnd_241848 : Nat := 4983230072969 + 3 ^ 40 * 241848 * 2
def baseEnd_241848 : Nat := 124184269328675002287767

theorem tailTrace_241848 : CollatzResearch.WordTrace tailWord_241848 prefixEnd_241848 124184269328675002287767 := by
  unfold tailWord_241848
  simp only [CollatzResearch.WordTrace]
  refine ⟨4410460613916737597551099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5880614151888983463401465 4410460613916737597551099)
  ·
    refine ⟨6615690920875106396326649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4410460613916737597551099 6615690920875106396326649)
    ·
      refine ⟨4961768190656329797244987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6615690920875106396326649 4961768190656329797244987)
      ·
        refine ⟨7442652285984494695867481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4961768190656329797244987 7442652285984494695867481)
        ·
          refine ⟨5581989214488371021900611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7442652285984494695867481 5581989214488371021900611)
          ·
            refine ⟨8372983821732556532850917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5581989214488371021900611 8372983821732556532850917)
            ·
              refine ⟨1569934466574854349909547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8372983821732556532850917 1569934466574854349909547)
              ·
                refine ⟨2354901699862281524864321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1569934466574854349909547 2354901699862281524864321)
                ·
                  refine ⟨1766176274896711143648241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2354901699862281524864321 1766176274896711143648241)
                  ·
                    refine ⟨1324632206172533357736181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1766176274896711143648241 1324632206172533357736181)
                    ·
                      refine ⟨124184269328675002287767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1324632206172533357736181 124184269328675002287767)
                      ·
                        rfl

theorem cell23_241848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_241848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_241848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_241848 prefixEnd_241848 := by exact prefixLift 241848
  have htrace : WordTrace (prefixWord ++ tailWord_241848) baseStart_241848 baseEnd_241848 := by
    simpa [prefixWord, tailWord_241848, baseEnd_241848] using wordTrace_append hprefix tailTrace_241848
  have hstable : (prefixWord ++ tailWord_241848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241848).length < 2 ^ (prefixWord ++ tailWord_241848).sum := by decide
  have hdescent : baseEnd_241848 < baseStart_241848 := by decide
  rcases family_descends (prefixWord ++ tailWord_241848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241925 : List Nat := [1, 3, 1, 1, 2, 1, 2, 4, 2, 3, 3]
def baseStart_241925 : Nat := 118140960795 + 241925 * 2 ^ 59
def prefixEnd_241925 : Nat := 4983230072969 + 3 ^ 40 * 241925 * 2
def baseEnd_241925 : Nat := 124223807339071201024913

theorem tailTrace_241925 : CollatzResearch.WordTrace tailWord_241925 prefixEnd_241925 124223807339071201024913 := by
  unfold tailWord_241925
  simp only [CollatzResearch.WordTrace]
  refine ⟨8823729648554517345655229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5882486432369678230436819 8823729648554517345655229)
  ·
    refine ⟨3308898618207944004620711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8823729648554517345655229 3308898618207944004620711)
    ·
      refine ⟨4963347927311916006931067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3308898618207944004620711 4963347927311916006931067)
      ·
        refine ⟨7445021890967874010396601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4963347927311916006931067 7445021890967874010396601)
        ·
          refine ⟨5583766418225905507797451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7445021890967874010396601 5583766418225905507797451)
          ·
            refine ⟨8375649627338858261696177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5583766418225905507797451 8375649627338858261696177)
            ·
              refine ⟨6281737220504143696272133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8375649627338858261696177 6281737220504143696272133)
              ·
                refine ⟨1177825728844526943051025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6281737220504143696272133 1177825728844526943051025)
                ·
                  refine ⟨883369296633395207288269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1177825728844526943051025 883369296633395207288269)
                  ·
                    refine ⟨331263486237523202733101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 883369296633395207288269 331263486237523202733101)
                    ·
                      refine ⟨124223807339071201024913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 331263486237523202733101 124223807339071201024913)
                      ·
                        rfl

theorem cell23_241925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 3, 3].length) (baseStart_241925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_241925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_241925 prefixEnd_241925 := by exact prefixLift 241925
  have htrace : WordTrace (prefixWord ++ tailWord_241925) baseStart_241925 baseEnd_241925 := by
    simpa [prefixWord, tailWord_241925, baseEnd_241925] using wordTrace_append hprefix tailTrace_241925
  have hstable : (prefixWord ++ tailWord_241925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241925).length < 2 ^ (prefixWord ++ tailWord_241925).sum := by decide
  have hdescent : baseEnd_241925 < baseStart_241925 := by decide
  rcases family_descends (prefixWord ++ tailWord_241925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241943 : List Nat := [1, 1, 3, 4, 1, 4, 2, 1, 2, 2, 2]
def baseStart_241943 : Nat := 118140960795 + 241943 * 2 ^ 59
def prefixEnd_241943 : Nat := 4983230072969 + 3 ^ 40 * 241943 * 2
def baseEnd_241943 : Nat := 124233049990852130599831

theorem tailTrace_241943 : CollatzResearch.WordTrace tailWord_241943 prefixEnd_241943 124233049990852130599831 := by
  unfold tailWord_241943
  simp only [CollatzResearch.WordTrace]
  refine ⟨8824386162489306419810483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5882924108326204279873655 8824386162489306419810483)
  ·
    refine ⟨13236579243733959629715725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8824386162489306419810483 13236579243733959629715725)
    ·
      refine ⟨4963717216400234861143397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13236579243733959629715725 4963717216400234861143397)
      ·
        refine ⟨930696978075044036464387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4963717216400234861143397 930696978075044036464387)
        ·
          refine ⟨1396045467112566054696581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 930696978075044036464387 1396045467112566054696581)
          ·
            refine ⟨261758525083606135255609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1396045467112566054696581 261758525083606135255609)
            ·
              refine ⟨196318893812704601441707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261758525083606135255609 196318893812704601441707)
              ·
                refine ⟨294478340719056902162561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196318893812704601441707 294478340719056902162561)
                ·
                  refine ⟨220858755539292676621921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 294478340719056902162561 220858755539292676621921)
                  ·
                    refine ⟨165644066654469507466441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 220858755539292676621921 165644066654469507466441)
                    ·
                      refine ⟨124233049990852130599831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 165644066654469507466441 124233049990852130599831)
                      ·
                        rfl

theorem cell23_241943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_241943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_241943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_241943 prefixEnd_241943 := by exact prefixLift 241943
  have htrace : WordTrace (prefixWord ++ tailWord_241943) baseStart_241943 baseEnd_241943 := by
    simpa [prefixWord, tailWord_241943, baseEnd_241943] using wordTrace_append hprefix tailTrace_241943
  have hstable : (prefixWord ++ tailWord_241943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241943).length < 2 ^ (prefixWord ++ tailWord_241943).sum := by decide
  have hdescent : baseEnd_241943 < baseStart_241943 := by decide
  rcases family_descends (prefixWord ++ tailWord_241943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241972 : List Nat := [2, 5, 1, 1, 1, 2, 1, 2, 1, 2, 5]
def baseStart_241972 : Nat := 118140960795 + 241972 * 2 ^ 59
def prefixEnd_241972 : Nat := 4983230072969 + 3 ^ 40 * 241972 * 2
def baseEnd_241972 : Nat := 124247940929832517137197

theorem tailTrace_241972 : CollatzResearch.WordTrace tailWord_241972 prefixEnd_241972 124247940929832517137197 := by
  unfold tailWord_241972
  simp only [CollatzResearch.WordTrace]
  refine ⟨4412721939692122186308085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5883629252922829581744113 4412721939692122186308085)
  ·
    refine ⟨413692681846136454966383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4412721939692122186308085 413692681846136454966383)
    ·
      refine ⟨620539022769204682449575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413692681846136454966383 620539022769204682449575)
      ·
        refine ⟨930808534153807023674363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 620539022769204682449575 930808534153807023674363)
        ·
          refine ⟨1396212801230710535511545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 930808534153807023674363 1396212801230710535511545)
          ·
            refine ⟨1047159600923032901633659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1396212801230710535511545 1047159600923032901633659)
            ·
              refine ⟨1570739401384549352450489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1047159600923032901633659 1570739401384549352450489)
              ·
                refine ⟨1178054551038412014337867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1570739401384549352450489 1178054551038412014337867)
                ·
                  refine ⟨1767081826557618021506801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1178054551038412014337867 1767081826557618021506801)
                  ·
                    refine ⟨1325311369918213516130101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1767081826557618021506801 1325311369918213516130101)
                    ·
                      refine ⟨124247940929832517137197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1325311369918213516130101 124247940929832517137197)
                      ·
                        rfl

theorem cell23_241972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_241972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_241972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_241972 prefixEnd_241972 := by exact prefixLift 241972
  have htrace : WordTrace (prefixWord ++ tailWord_241972) baseStart_241972 baseEnd_241972 := by
    simpa [prefixWord, tailWord_241972, baseEnd_241972] using wordTrace_append hprefix tailTrace_241972
  have hstable : (prefixWord ++ tailWord_241972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241972).length < 2 ^ (prefixWord ++ tailWord_241972).sum := by decide
  have hdescent : baseEnd_241972 < baseStart_241972 := by decide
  rcases family_descends (prefixWord ++ tailWord_241972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242002 : List Nat := [3, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3]
def baseStart_242002 : Nat := 118140960795 + 242002 * 2 ^ 59
def prefixEnd_242002 : Nat := 4983230072969 + 3 ^ 40 * 242002 * 2
def baseEnd_242002 : Nat := 124263345349467399762059

theorem tailTrace_242002 : CollatzResearch.WordTrace tailWord_242002 prefixEnd_242002 124263345349467399762059 := by
  unfold tailWord_242002
  simp only [CollatzResearch.WordTrace]
  refine ⟨2206634517318889874052065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5884358712850372997472173 2206634517318889874052065)
  ·
    refine ⟨1654975887989167405539049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2206634517318889874052065 1654975887989167405539049)
    ·
      refine ⟨1241231915991875554154287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1654975887989167405539049 1241231915991875554154287)
      ·
        refine ⟨1861847873987813331231431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1241231915991875554154287 1861847873987813331231431)
        ·
          refine ⟨2792771810981719996847147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1861847873987813331231431 2792771810981719996847147)
          ·
            refine ⟨4189157716472579995270721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2792771810981719996847147 4189157716472579995270721)
            ·
              refine ⟨3141868287354434996453041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4189157716472579995270721 3141868287354434996453041)
              ·
                refine ⟨2356401215515826247339781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3141868287354434996453041 2356401215515826247339781)
                ·
                  refine ⟨441825227909217421376209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2356401215515826247339781 441825227909217421376209)
                  ·
                    refine ⟨331368920931913066032157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 441825227909217421376209 331368920931913066032157)
                    ·
                      refine ⟨124263345349467399762059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 331368920931913066032157 124263345349467399762059)
                      ·
                        rfl

theorem cell23_242002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_242002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242002 prefixEnd_242002 := by exact prefixLift 242002
  have htrace : WordTrace (prefixWord ++ tailWord_242002) baseStart_242002 baseEnd_242002 := by
    simpa [prefixWord, tailWord_242002, baseEnd_242002] using wordTrace_append hprefix tailTrace_242002
  have hstable : (prefixWord ++ tailWord_242002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242002).length < 2 ^ (prefixWord ++ tailWord_242002).sum := by decide
  have hdescent : baseEnd_242002 < baseStart_242002 := by decide
  rcases family_descends (prefixWord ++ tailWord_242002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242016 : List Nat := [2, 1, 1, 3, 6, 1, 1, 1, 2, 1, 4]
def baseStart_242016 : Nat := 118140960795 + 242016 * 2 ^ 59
def prefixEnd_242016 : Nat := 4983230072969 + 3 ^ 40 * 242016 * 2
def baseEnd_242016 : Nat := 124270534078630344986995

theorem tailTrace_242016 : CollatzResearch.WordTrace tailWord_242016 prefixEnd_242016 124270534078630344986995 := by
  unfold tailWord_242016
  simp only [CollatzResearch.WordTrace]
  refine ⟨4413524345612419943608951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5884699127483226591478601 4413524345612419943608951)
  ·
    refine ⟨6620286518418629915413427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4413524345612419943608951 6620286518418629915413427)
    ·
      refine ⟨9930429777627944873120141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6620286518418629915413427 9930429777627944873120141)
      ·
        refine ⟨3723911166610479327420053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9930429777627944873120141 3723911166610479327420053)
        ·
          refine ⟨174558335934866218472815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3723911166610479327420053 174558335934866218472815)
          ·
            refine ⟨261837503902299327709223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174558335934866218472815 261837503902299327709223)
            ·
              refine ⟨392756255853448991563835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261837503902299327709223 392756255853448991563835)
              ·
                refine ⟨589134383780173487345753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 392756255853448991563835 589134383780173487345753)
                ·
                  refine ⟨441850787835130115509315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 589134383780173487345753 441850787835130115509315)
                  ·
                    refine ⟨662776181752695173263973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 441850787835130115509315 662776181752695173263973)
                    ·
                      refine ⟨124270534078630344986995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 662776181752695173263973 124270534078630344986995)
                      ·
                        rfl

theorem cell23_242016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 2, 1, 4].length) (baseStart_242016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242016 prefixEnd_242016 := by exact prefixLift 242016
  have htrace : WordTrace (prefixWord ++ tailWord_242016) baseStart_242016 baseEnd_242016 := by
    simpa [prefixWord, tailWord_242016, baseEnd_242016] using wordTrace_append hprefix tailTrace_242016
  have hstable : (prefixWord ++ tailWord_242016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242016).length < 2 ^ (prefixWord ++ tailWord_242016).sum := by decide
  have hdescent : baseEnd_242016 < baseStart_242016 := by decide
  rcases family_descends (prefixWord ++ tailWord_242016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242026 : List Nat := [3, 1, 3, 3, 1, 1, 1, 5, 1, 4]
def baseStart_242026 : Nat := 118140960795 + 242026 * 2 ^ 59
def prefixEnd_242026 : Nat := 4983230072969 + 3 ^ 40 * 242026 * 2
def baseEnd_242026 : Nat := 41425222961725101953983

theorem tailTrace_242026 : CollatzResearch.WordTrace tailWord_242026 prefixEnd_242026 41425222961725101953983 := by
  unfold tailWord_242026
  simp only [CollatzResearch.WordTrace]
  refine ⟨2206853355297152898770483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5884942280792407730054621 2206853355297152898770483)
  ·
    refine ⟨3310280032945729348155725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2206853355297152898770483 3310280032945729348155725)
    ·
      refine ⟨1241355012354648505558397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3310280032945729348155725 1241355012354648505558397)
      ·
        refine ⟨465508129632993189584399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1241355012354648505558397 465508129632993189584399)
        ·
          refine ⟨698262194449489784376599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465508129632993189584399 698262194449489784376599)
          ·
            refine ⟨1047393291674234676564899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 698262194449489784376599 1047393291674234676564899)
            ·
              refine ⟨1571089937511352014847349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1047393291674234676564899 1571089937511352014847349)
              ·
                refine ⟨147289681641689251391939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1571089937511352014847349 147289681641689251391939)
                ·
                  refine ⟨220934522462533877087909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147289681641689251391939 220934522462533877087909)
                  ·
                    refine ⟨41425222961725101953983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 220934522462533877087909 41425222961725101953983)
                    ·
                      rfl

theorem cell23_242026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_242026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242026 prefixEnd_242026 := by exact prefixLift 242026
  have htrace : WordTrace (prefixWord ++ tailWord_242026) baseStart_242026 baseEnd_242026 := by
    simpa [prefixWord, tailWord_242026, baseEnd_242026] using wordTrace_append hprefix tailTrace_242026
  have hstable : (prefixWord ++ tailWord_242026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242026).length < 2 ^ (prefixWord ++ tailWord_242026).sum := by decide
  have hdescent : baseEnd_242026 < baseStart_242026 := by decide
  rcases family_descends (prefixWord ++ tailWord_242026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242042 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 5, 5, 2]
def baseStart_242042 : Nat := 118140960795 + 242042 * 2 ^ 59
def prefixEnd_242042 : Nat := 4983230072969 + 3 ^ 40 * 242042 * 2
def baseEnd_242042 : Nat := 124283884575647243261875

theorem tailTrace_242042 : CollatzResearch.WordTrace tailWord_242042 prefixEnd_242042 124283884575647243261875 := by
  unfold tailWord_242042
  simp only [CollatzResearch.WordTrace]
  refine ⟨2206999247282661581916095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5885331326087097551776253 2206999247282661581916095)
  ·
    refine ⟨3310498870923992372874143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2206999247282661581916095 3310498870923992372874143)
    ·
      refine ⟨4965748306385988559311215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3310498870923992372874143 4965748306385988559311215)
      ·
        refine ⟨7448622459578982838966823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4965748306385988559311215 7448622459578982838966823)
        ·
          refine ⟨11172933689368474258450235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7448622459578982838966823 11172933689368474258450235)
          ·
            refine ⟨16759400534052711387675353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11172933689368474258450235 16759400534052711387675353)
            ·
              refine ⟨12569550400539533540756515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16759400534052711387675353 12569550400539533540756515)
              ·
                refine ⟨18854325600809300311134773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12569550400539533540756515 18854325600809300311134773)
                ·
                  refine ⟨1767593025075871904168885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18854325600809300311134773 1767593025075871904168885)
                  ·
                    refine ⟨165711846100862991015833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1767593025075871904168885 165711846100862991015833)
                    ·
                      refine ⟨124283884575647243261875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 165711846100862991015833 124283884575647243261875)
                      ·
                        rfl

theorem cell23_242042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 5, 5, 2].length) (baseStart_242042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242042 prefixEnd_242042 := by exact prefixLift 242042
  have htrace : WordTrace (prefixWord ++ tailWord_242042) baseStart_242042 baseEnd_242042 := by
    simpa [prefixWord, tailWord_242042, baseEnd_242042] using wordTrace_append hprefix tailTrace_242042
  have hstable : (prefixWord ++ tailWord_242042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242042).length < 2 ^ (prefixWord ++ tailWord_242042).sum := by decide
  have hdescent : baseEnd_242042 < baseStart_242042 := by decide
  rcases family_descends (prefixWord ++ tailWord_242042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242082 : List Nat := [3, 3, 1, 2, 1, 1, 2, 1, 3, 6]
def baseStart_242082 : Nat := 118140960795 + 242082 * 2 ^ 59
def prefixEnd_242082 : Nat := 4983230072969 + 3 ^ 40 * 242082 * 2
def baseEnd_242082 : Nat := 41434807933942362253897

theorem tailTrace_242082 : CollatzResearch.WordTrace tailWord_242082 prefixEnd_242082 41434807933942362253897 := by
  unfold tailWord_242082
  simp only [CollatzResearch.WordTrace]
  refine ⟨2207363977246433289780125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5886303939323822106080333 2207363977246433289780125)
  ·
    refine ⟨827761491467412483667547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2207363977246433289780125 827761491467412483667547)
    ·
      refine ⟨1241642237201118725501321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 827761491467412483667547 1241642237201118725501321)
      ·
        refine ⟨931231677900839044125991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1241642237201118725501321 931231677900839044125991)
        ·
          refine ⟨1396847516851258566188987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 931231677900839044125991 1396847516851258566188987)
          ·
            refine ⟨2095271275276887849283481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1396847516851258566188987 2095271275276887849283481)
            ·
              refine ⟨1571453456457665886962611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2095271275276887849283481 1571453456457665886962611)
              ·
                refine ⟨2357180184686498830443917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1571453456457665886962611 2357180184686498830443917)
                ·
                  refine ⟨883942569257437061416469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2357180184686498830443917 883942569257437061416469)
                  ·
                    refine ⟨41434807933942362253897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 883942569257437061416469 41434807933942362253897)
                    ·
                      rfl

theorem cell23_242082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_242082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242082 prefixEnd_242082 := by exact prefixLift 242082
  have htrace : WordTrace (prefixWord ++ tailWord_242082) baseStart_242082 baseEnd_242082 := by
    simpa [prefixWord, tailWord_242082, baseEnd_242082] using wordTrace_append hprefix tailTrace_242082
  have hstable : (prefixWord ++ tailWord_242082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242082).length < 2 ^ (prefixWord ++ tailWord_242082).sum := by decide
  have hdescent : baseEnd_242082 < baseStart_242082 := by decide
  rcases family_descends (prefixWord ++ tailWord_242082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242083 : List Nat := [1, 1, 1, 4, 1, 6, 1, 3, 1, 1, 3]
def baseStart_242083 : Nat := 118140960795 + 242083 * 2 ^ 59
def prefixEnd_242083 : Nat := 4983230072969 + 3 ^ 40 * 242083 * 2
def baseEnd_242083 : Nat := 124304937282481582849187

theorem tailTrace_242083 : CollatzResearch.WordTrace tailWord_242083 prefixEnd_242083 124304937282481582849187 := by
  unfold tailWord_242083
  simp only [CollatzResearch.WordTrace]
  refine ⟨8829492381982110329906903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5886328254654740219937935 8829492381982110329906903)
  ·
    refine ⟨13244238572973165494860355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8829492381982110329906903 13244238572973165494860355)
    ·
      refine ⟨19866357859459748242290533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13244238572973165494860355 19866357859459748242290533)
      ·
        refine ⟨3724942098648702795429475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19866357859459748242290533 3724942098648702795429475)
        ·
          refine ⟨5587413147973054193144213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3724942098648702795429475 5587413147973054193144213)
          ·
            refine ⟨261909991311236915303635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5587413147973054193144213 261909991311236915303635)
            ·
              refine ⟨392864986966855372955453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261909991311236915303635 392864986966855372955453)
              ·
                refine ⟨147324370112570764858295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 392864986966855372955453 147324370112570764858295)
                ·
                  refine ⟨220986555168856147287443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147324370112570764858295 220986555168856147287443)
                  ·
                    refine ⟨331479832753284220931165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 220986555168856147287443 331479832753284220931165)
                    ·
                      refine ⟨124304937282481582849187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 331479832753284220931165 124304937282481582849187)
                      ·
                        rfl

theorem cell23_242083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 3, 1, 1, 3].length) (baseStart_242083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242083 prefixEnd_242083 := by exact prefixLift 242083
  have htrace : WordTrace (prefixWord ++ tailWord_242083) baseStart_242083 baseEnd_242083 := by
    simpa [prefixWord, tailWord_242083, baseEnd_242083] using wordTrace_append hprefix tailTrace_242083
  have hstable : (prefixWord ++ tailWord_242083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242083).length < 2 ^ (prefixWord ++ tailWord_242083).sum := by decide
  have hdescent : baseEnd_242083 < baseStart_242083 := by decide
  rcases family_descends (prefixWord ++ tailWord_242083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242089 : List Nat := [1, 2, 1, 1, 1, 1, 3, 4, 5, 2, 2]
def baseStart_242089 : Nat := 118140960795 + 242089 * 2 ^ 59
def prefixEnd_242089 : Nat := 4983230072969 + 3 ^ 40 * 242089 * 2
def baseEnd_242089 : Nat := 124308018166408559374159

theorem tailTrace_242089 : CollatzResearch.WordTrace tailWord_242089 prefixEnd_242089 124308018166408559374159 := by
  unfold tailWord_242089
  simp only [CollatzResearch.WordTrace]
  refine ⟨8829711219960373354625321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5886474146640248903083547 8829711219960373354625321)
  ·
    refine ⟨6622283414970280015968991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8829711219960373354625321 6622283414970280015968991)
    ·
      refine ⟨9933425122455420023953487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6622283414970280015968991 9933425122455420023953487)
      ·
        refine ⟨14900137683683130035930231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9933425122455420023953487 14900137683683130035930231)
        ·
          refine ⟨22350206525524695053895347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14900137683683130035930231 22350206525524695053895347)
          ·
            refine ⟨33525309788287042580843021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22350206525524695053895347 33525309788287042580843021)
            ·
              refine ⟨12571991170607640967816133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33525309788287042580843021 12571991170607640967816133)
              ·
                refine ⟨2357248344488932681465525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12571991170607640967816133 2357248344488932681465525)
                ·
                  refine ⟨220992032295837438887393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2357248344488932681465525 220992032295837438887393)
                  ·
                    refine ⟨165744024221878079165545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 220992032295837438887393 165744024221878079165545)
                    ·
                      refine ⟨124308018166408559374159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 165744024221878079165545 124308018166408559374159)
                      ·
                        rfl

theorem cell23_242089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 5, 2, 2].length) (baseStart_242089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242089 prefixEnd_242089 := by exact prefixLift 242089
  have htrace : WordTrace (prefixWord ++ tailWord_242089) baseStart_242089 baseEnd_242089 := by
    simpa [prefixWord, tailWord_242089, baseEnd_242089] using wordTrace_append hprefix tailTrace_242089
  have hstable : (prefixWord ++ tailWord_242089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242089).length < 2 ^ (prefixWord ++ tailWord_242089).sum := by decide
  have hdescent : baseEnd_242089 < baseStart_242089 := by decide
  rcases family_descends (prefixWord ++ tailWord_242089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242092 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 3]
def baseStart_242092 : Nat := 118140960795 + 242092 * 2 ^ 59
def prefixEnd_242092 : Nat := 4983230072969 + 3 ^ 40 * 242092 * 2
def baseEnd_242092 : Nat := 124309558608372047636645

theorem tailTrace_242092 : CollatzResearch.WordTrace tailWord_242092 prefixEnd_242092 124309558608372047636645 := by
  unfold tailWord_242092
  simp only [CollatzResearch.WordTrace]
  refine ⟨4414910319474752433492265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5886547092633003244656353 4414910319474752433492265)
  ·
    refine ⟨3311182739606064325119199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4414910319474752433492265 3311182739606064325119199)
    ·
      refine ⟨4966774109409096487678799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3311182739606064325119199 4966774109409096487678799)
      ·
        refine ⟨7450161164113644731518199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4966774109409096487678799 7450161164113644731518199)
        ·
          refine ⟨11175241746170467097277299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7450161164113644731518199 11175241746170467097277299)
          ·
            refine ⟨16762862619255700645915949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11175241746170467097277299 16762862619255700645915949)
            ·
              refine ⟨6286073482220887742218481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16762862619255700645915949 6286073482220887742218481)
              ·
                refine ⟨4714555111665665806663861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6286073482220887742218481 4714555111665665806663861)
                ·
                  refine ⟨441989541718656169374737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4714555111665665806663861 441989541718656169374737)
                  ·
                    refine ⟨331492156288992127031053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 441989541718656169374737 331492156288992127031053)
                    ·
                      refine ⟨124309558608372047636645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 331492156288992127031053 124309558608372047636645)
                      ·
                        rfl

theorem cell23_242092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 3].length) (baseStart_242092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242092 prefixEnd_242092 := by exact prefixLift 242092
  have htrace : WordTrace (prefixWord ++ tailWord_242092) baseStart_242092 baseEnd_242092 := by
    simpa [prefixWord, tailWord_242092, baseEnd_242092] using wordTrace_append hprefix tailTrace_242092
  have hstable : (prefixWord ++ tailWord_242092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242092).length < 2 ^ (prefixWord ++ tailWord_242092).sum := by decide
  have hdescent : baseEnd_242092 < baseStart_242092 := by decide
  rcases family_descends (prefixWord ++ tailWord_242092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242093 : List Nat := [1, 5, 2, 2, 2, 1, 1, 2, 2, 3, 2]
def baseStart_242093 : Nat := 118140960795 + 242093 * 2 ^ 59
def prefixEnd_242093 : Nat := 4983230072969 + 3 ^ 40 * 242093 * 2
def baseEnd_242093 : Nat := 124310072089026543724141

theorem tailTrace_242093 : CollatzResearch.WordTrace tailWord_242093 prefixEnd_242093 124310072089026543724141 := by
  unfold tailWord_242093
  simp only [CollatzResearch.WordTrace]
  refine ⟨8829857111945882037770933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5886571407963921358513955 8829857111945882037770933)
  ·
    refine ⟨827799104244926441041025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8829857111945882037770933 827799104244926441041025)
    ·
      refine ⟨620849328183694830780769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 827799104244926441041025 620849328183694830780769)
      ·
        refine ⟨465636996137771123085577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 620849328183694830780769 465636996137771123085577)
        ·
          refine ⟨349227747103328342314183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 465636996137771123085577 349227747103328342314183)
          ·
            refine ⟨523841620654992513471275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349227747103328342314183 523841620654992513471275)
            ·
              refine ⟨785762430982488770206913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523841620654992513471275 785762430982488770206913)
              ·
                refine ⟨589321823236866577655185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 785762430982488770206913 589321823236866577655185)
                ·
                  refine ⟨441991367427649933241389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 589321823236866577655185 441991367427649933241389)
                  ·
                    refine ⟨165746762785368724965521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 441991367427649933241389 165746762785368724965521)
                    ·
                      refine ⟨124310072089026543724141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 165746762785368724965521 124310072089026543724141)
                      ·
                        rfl

theorem cell23_242093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_242093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242093 prefixEnd_242093 := by exact prefixLift 242093
  have htrace : WordTrace (prefixWord ++ tailWord_242093) baseStart_242093 baseEnd_242093 := by
    simpa [prefixWord, tailWord_242093, baseEnd_242093] using wordTrace_append hprefix tailTrace_242093
  have hstable : (prefixWord ++ tailWord_242093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242093).length < 2 ^ (prefixWord ++ tailWord_242093).sum := by decide
  have hdescent : baseEnd_242093 < baseStart_242093 := by decide
  rcases family_descends (prefixWord ++ tailWord_242093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242115 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 6]
def baseStart_242115 : Nat := 118140960795 + 242115 * 2 ^ 59
def prefixEnd_242115 : Nat := 4983230072969 + 3 ^ 40 * 242115 * 2
def baseEnd_242115 : Nat := 124321368663425457649039

theorem tailTrace_242115 : CollatzResearch.WordTrace tailWord_242115 prefixEnd_242115 124321368663425457649039 := by
  unfold tailWord_242115
  simp only [CollatzResearch.WordTrace]
  refine ⟨8830659517866179795071799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5887106345244119863381199 8830659517866179795071799)
  ·
    refine ⟨13245989276799269692607699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8830659517866179795071799 13245989276799269692607699)
    ·
      refine ⟨19868983915198904538911549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13245989276799269692607699 19868983915198904538911549)
      ·
        refine ⟨7450868968199589202091831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19868983915198904538911549 7450868968199589202091831)
        ·
          refine ⟨11176303452299383803137747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7450868968199589202091831 11176303452299383803137747)
          ·
            refine ⟨16764455178449075704706621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11176303452299383803137747 16764455178449075704706621)
            ·
              refine ⟨6286670691918403389264983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16764455178449075704706621 6286670691918403389264983)
              ·
                refine ⟨9430006037877605083897475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6286670691918403389264983 9430006037877605083897475)
                ·
                  refine ⟨14145009056816407625846213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9430006037877605083897475 14145009056816407625846213)
                  ·
                    refine ⟨2652189198153076429846165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14145009056816407625846213 2652189198153076429846165)
                    ·
                      refine ⟨124321368663425457649039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2652189198153076429846165 124321368663425457649039)
                      ·
                        rfl

theorem cell23_242115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_242115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242115 prefixEnd_242115 := by exact prefixLift 242115
  have htrace : WordTrace (prefixWord ++ tailWord_242115) baseStart_242115 baseEnd_242115 := by
    simpa [prefixWord, tailWord_242115, baseEnd_242115] using wordTrace_append hprefix tailTrace_242115
  have hstable : (prefixWord ++ tailWord_242115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242115).length < 2 ^ (prefixWord ++ tailWord_242115).sum := by decide
  have hdescent : baseEnd_242115 < baseStart_242115 := by decide
  rcases family_descends (prefixWord ++ tailWord_242115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242146 : List Nat := [3, 3, 3, 2, 2, 10]
def baseStart_242146 : Nat := 118140960795 + 242146 * 2 ^ 59
def prefixEnd_242146 : Nat := 4983230072969 + 3 ^ 40 * 242146 * 2
def baseEnd_242146 : Nat := 511676076393888215479

theorem tailTrace_242146 : CollatzResearch.WordTrace tailWord_242146 prefixEnd_242146 511676076393888215479 := by
  unfold tailWord_242146
  simp only [CollatzResearch.WordTrace]
  refine ⟨2207947545188468022362573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5887860120502581392966861 2207947545188468022362573)
  ·
    refine ⟨827980329445675508385965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2207947545188468022362573 827980329445675508385965)
    ·
      refine ⟨310492623542128315644737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 827980329445675508385965 310492623542128315644737)
      ·
        refine ⟨232869467656596236733553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310492623542128315644737 232869467656596236733553)
        ·
          refine ⟨174652100742447177550165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232869467656596236733553 174652100742447177550165)
          ·
            refine ⟨511676076393888215479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 174652100742447177550165 511676076393888215479)
            ·
              rfl

theorem cell23_242146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 10].length) (baseStart_242146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242146 prefixEnd_242146 := by exact prefixLift 242146
  have htrace : WordTrace (prefixWord ++ tailWord_242146) baseStart_242146 baseEnd_242146 := by
    simpa [prefixWord, tailWord_242146, baseEnd_242146] using wordTrace_append hprefix tailTrace_242146
  have hstable : (prefixWord ++ tailWord_242146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242146).length < 2 ^ (prefixWord ++ tailWord_242146).sum := by decide
  have hdescent : baseEnd_242146 < baseStart_242146 := by decide
  rcases family_descends (prefixWord ++ tailWord_242146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242156 : List Nat := [2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 3]
def baseStart_242156 : Nat := 118140960795 + 242156 * 2 ^ 59
def prefixEnd_242156 : Nat := 4983230072969 + 3 ^ 40 * 242156 * 2
def baseEnd_242156 : Nat := 124342421370259797236351

theorem tailTrace_242156 : CollatzResearch.WordTrace tailWord_242156 prefixEnd_242156 124342421370259797236351 := by
  unfold tailWord_242156
  simp only [CollatzResearch.WordTrace]
  refine ⟨4416077455358821898657161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5888103273811762531542881 4416077455358821898657161)
  ·
    refine ⟨3312058091519116423992871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4416077455358821898657161 3312058091519116423992871)
    ·
      refine ⟨4968087137278674635989307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3312058091519116423992871 4968087137278674635989307)
      ·
        refine ⟨7452130705918011953983961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4968087137278674635989307 7452130705918011953983961)
        ·
          refine ⟨5589098029438508965487971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7452130705918011953983961 5589098029438508965487971)
          ·
            refine ⟨8383647044157763448231957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5589098029438508965487971 8383647044157763448231957)
            ·
              refine ⟨392983455194895161635873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8383647044157763448231957 392983455194895161635873)
              ·
                refine ⟨294737591396171371226905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 392983455194895161635873 294737591396171371226905)
                ·
                  refine ⟨221053193547128528420179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 294737591396171371226905 221053193547128528420179)
                  ·
                    refine ⟨331579790320692792630269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 221053193547128528420179 331579790320692792630269)
                    ·
                      refine ⟨124342421370259797236351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 331579790320692792630269 124342421370259797236351)
                      ·
                        rfl

theorem cell23_242156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 3].length) (baseStart_242156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242156 prefixEnd_242156 := by exact prefixLift 242156
  have htrace : WordTrace (prefixWord ++ tailWord_242156) baseStart_242156 baseEnd_242156 := by
    simpa [prefixWord, tailWord_242156, baseEnd_242156] using wordTrace_append hprefix tailTrace_242156
  have hstable : (prefixWord ++ tailWord_242156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242156).length < 2 ^ (prefixWord ++ tailWord_242156).sum := by decide
  have hdescent : baseEnd_242156 < baseStart_242156 := by decide
  rcases family_descends (prefixWord ++ tailWord_242156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242157 : List Nat := [1, 5, 1, 3, 1, 1, 4, 2, 1, 2, 2]
def baseStart_242157 : Nat := 118140960795 + 242157 * 2 ^ 59
def prefixEnd_242157 : Nat := 4983230072969 + 3 ^ 40 * 242157 * 2
def baseEnd_242157 : Nat := 124342934850914293323847

theorem tailTrace_242157 : CollatzResearch.WordTrace tailWord_242157 prefixEnd_242157 124342934850914293323847 := by
  unfold tailWord_242157
  simp only [CollatzResearch.WordTrace]
  refine ⟨8832191383714020968100725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5888127589142680645400483 8832191383714020968100725)
  ·
    refine ⟨828017942223189465759443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8832191383714020968100725 828017942223189465759443)
    ·
      refine ⟨1242026913334784198639165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 828017942223189465759443 1242026913334784198639165)
      ·
        refine ⟨465760092500544074489687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1242026913334784198639165 465760092500544074489687)
        ·
          refine ⟨698640138750816111734531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465760092500544074489687 698640138750816111734531)
          ·
            refine ⟨1047960208126224167601797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 698640138750816111734531 1047960208126224167601797)
            ·
              refine ⟨196492539023667031425337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1047960208126224167601797 196492539023667031425337)
              ·
                refine ⟨147369404267750273569003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196492539023667031425337 147369404267750273569003)
                ·
                  refine ⟨221054106401625410353505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147369404267750273569003 221054106401625410353505)
                  ·
                    refine ⟨165790579801219057765129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 221054106401625410353505 165790579801219057765129)
                    ·
                      refine ⟨124342934850914293323847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 165790579801219057765129 124342934850914293323847)
                      ·
                        rfl

theorem cell23_242157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_242157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242157 prefixEnd_242157 := by exact prefixLift 242157
  have htrace : WordTrace (prefixWord ++ tailWord_242157) baseStart_242157 baseEnd_242157 := by
    simpa [prefixWord, tailWord_242157, baseEnd_242157] using wordTrace_append hprefix tailTrace_242157
  have hstable : (prefixWord ++ tailWord_242157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242157).length < 2 ^ (prefixWord ++ tailWord_242157).sum := by decide
  have hdescent : baseEnd_242157 < baseStart_242157 := by decide
  rcases family_descends (prefixWord ++ tailWord_242157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242166 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2]
def baseStart_242166 : Nat := 118140960795 + 242166 * 2 ^ 59
def prefixEnd_242166 : Nat := 4983230072969 + 3 ^ 40 * 242166 * 2
def baseEnd_242166 : Nat := 124347556176804758111305

theorem tailTrace_242166 : CollatzResearch.WordTrace tailWord_242166 prefixEnd_242166 124347556176804758111305 := by
  unfold tailWord_242166
  simp only [CollatzResearch.WordTrace]
  refine ⟨552032477542588469073647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5888346427120943670118901 552032477542588469073647)
  ·
    refine ⟨828048716313882703610471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 552032477542588469073647 828048716313882703610471)
    ·
      refine ⟨1242073074470824055415707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 828048716313882703610471 1242073074470824055415707)
      ·
        refine ⟨1863109611706236083123561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1242073074470824055415707 1863109611706236083123561)
        ·
          refine ⟨1397332208779677062342671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1863109611706236083123561 1397332208779677062342671)
          ·
            refine ⟨2095998313169515593514007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1397332208779677062342671 2095998313169515593514007)
            ·
              refine ⟨3143997469754273390271011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2095998313169515593514007 3143997469754273390271011)
              ·
                refine ⟨4715996204631410085406517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3143997469754273390271011 4715996204631410085406517)
                ·
                  refine ⟨442124644184194695506861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4715996204631410085406517 442124644184194695506861)
                  ·
                    refine ⟨165796741569073010815073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 442124644184194695506861 165796741569073010815073)
                    ·
                      refine ⟨124347556176804758111305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 165796741569073010815073 124347556176804758111305)
                      ·
                        rfl

theorem cell23_242166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2].length) (baseStart_242166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242166 prefixEnd_242166 := by exact prefixLift 242166
  have htrace : WordTrace (prefixWord ++ tailWord_242166) baseStart_242166 baseEnd_242166 := by
    simpa [prefixWord, tailWord_242166, baseEnd_242166] using wordTrace_append hprefix tailTrace_242166
  have hstable : (prefixWord ++ tailWord_242166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242166).length < 2 ^ (prefixWord ++ tailWord_242166).sum := by decide
  have hdescent : baseEnd_242166 < baseStart_242166 := by decide
  rcases family_descends (prefixWord ++ tailWord_242166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242200 : List Nat := [2, 1, 2, 3, 3, 3, 2, 1, 1, 3, 2]
def baseStart_242200 : Nat := 118140960795 + 242200 * 2 ^ 59
def prefixEnd_242200 : Nat := 4983230072969 + 3 ^ 40 * 242200 * 2
def baseEnd_242200 : Nat := 124365014519057625086149

theorem tailTrace_242200 : CollatzResearch.WordTrace tailWord_242200 prefixEnd_242200 124365014519057625086149 := by
  unfold tailWord_242200
  simp only [CollatzResearch.WordTrace]
  refine ⟨4416879861279119655958027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5889173148372159541277369 4416879861279119655958027)
  ·
    refine ⟨6625319791918679483937041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4416879861279119655958027 6625319791918679483937041)
    ·
      refine ⟨4968989843939009612952781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6625319791918679483937041 4968989843939009612952781)
      ·
        refine ⟨1863371191477128604857293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4968989843939009612952781 1863371191477128604857293)
        ·
          refine ⟨698764196803923226821485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1863371191477128604857293 698764196803923226821485)
          ·
            refine ⟨262036573801471210058057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 698764196803923226821485 262036573801471210058057)
            ·
              refine ⟨196527430351103407543543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262036573801471210058057 196527430351103407543543)
              ·
                refine ⟨294791145526655111315315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196527430351103407543543 294791145526655111315315)
                ·
                  refine ⟨442186718289982666972973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 294791145526655111315315 442186718289982666972973)
                  ·
                    refine ⟨165820019358743500114865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 442186718289982666972973 165820019358743500114865)
                    ·
                      refine ⟨124365014519057625086149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 165820019358743500114865 124365014519057625086149)
                      ·
                        rfl

theorem cell23_242200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 1, 1, 3, 2].length) (baseStart_242200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242200 prefixEnd_242200 := by exact prefixLift 242200
  have htrace : WordTrace (prefixWord ++ tailWord_242200) baseStart_242200 baseEnd_242200 := by
    simpa [prefixWord, tailWord_242200, baseEnd_242200] using wordTrace_append hprefix tailTrace_242200
  have hstable : (prefixWord ++ tailWord_242200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242200).length < 2 ^ (prefixWord ++ tailWord_242200).sum := by decide
  have hdescent : baseEnd_242200 < baseStart_242200 := by decide
  rcases family_descends (prefixWord ++ tailWord_242200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242213 : List Nat := [1, 3, 1, 2, 2, 1, 5, 2, 2, 2, 2]
def baseStart_242213 : Nat := 118140960795 + 242213 * 2 ^ 59
def prefixEnd_242213 : Nat := 4983230072969 + 3 ^ 40 * 242213 * 2
def baseEnd_242213 : Nat := 124371689767566074223589

theorem tailTrace_242213 : CollatzResearch.WordTrace tailWord_242213 prefixEnd_242213 124371689767566074223589 := by
  unfold tailWord_242213
  simp only [CollatzResearch.WordTrace]
  refine ⟨8834233871511142532139293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5889489247674095021426195 8834233871511142532139293)
  ·
    refine ⟨3312837701816678449552235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8834233871511142532139293 3312837701816678449552235)
    ·
      refine ⟨4969256552725017674328353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3312837701816678449552235 4969256552725017674328353)
      ·
        refine ⟨3726942414543763255746265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4969256552725017674328353 3726942414543763255746265)
        ·
          refine ⟨2795206810907822441809699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3726942414543763255746265 2795206810907822441809699)
          ·
            refine ⟨4192810216361733662714549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2795206810907822441809699 4192810216361733662714549)
            ·
              refine ⟨393075957783912530879489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4192810216361733662714549 393075957783912530879489)
              ·
                refine ⟨294806968337934398159617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 393075957783912530879489 294806968337934398159617)
                ·
                  refine ⟨221105226253450798619713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 294806968337934398159617 221105226253450798619713)
                  ·
                    refine ⟨165828919690088098964785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 221105226253450798619713 165828919690088098964785)
                    ·
                      refine ⟨124371689767566074223589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 165828919690088098964785 124371689767566074223589)
                      ·
                        rfl

theorem cell23_242213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2, 2, 2, 2].length) (baseStart_242213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242213 prefixEnd_242213 := by exact prefixLift 242213
  have htrace : WordTrace (prefixWord ++ tailWord_242213) baseStart_242213 baseEnd_242213 := by
    simpa [prefixWord, tailWord_242213, baseEnd_242213] using wordTrace_append hprefix tailTrace_242213
  have hstable : (prefixWord ++ tailWord_242213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242213).length < 2 ^ (prefixWord ++ tailWord_242213).sum := by decide
  have hdescent : baseEnd_242213 < baseStart_242213 := by decide
  rcases family_descends (prefixWord ++ tailWord_242213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242229 : List Nat := [1, 3, 3, 1, 1, 2, 1, 3, 2, 3, 3]
def baseStart_242229 : Nat := 118140960795 + 242229 * 2 ^ 59
def prefixEnd_242229 : Nat := 4983230072969 + 3 ^ 40 * 242229 * 2
def baseEnd_242229 : Nat := 124379905458038011623515

theorem tailTrace_242229 : CollatzResearch.WordTrace tailWord_242229 prefixEnd_242229 124379905458038011623515 := by
  unfold tailWord_242229
  simp only [CollatzResearch.WordTrace]
  refine ⟨8834817439453177264721741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5889878292968784843147827 8834817439453177264721741)
  ·
    refine ⟨3313056539794941474270653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8834817439453177264721741 3313056539794941474270653)
    ·
      refine ⟨1242396202423103052851495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3313056539794941474270653 1242396202423103052851495)
      ·
        refine ⟨1863594303634654579277243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1242396202423103052851495 1863594303634654579277243)
        ·
          refine ⟨2795391455451981868915865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1863594303634654579277243 2795391455451981868915865)
          ·
            refine ⟨2096543591588986401686899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2795391455451981868915865 2096543591588986401686899)
            ·
              refine ⟨3144815387383479602530349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2096543591588986401686899 3144815387383479602530349)
              ·
                refine ⟨1179305770268804850948881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3144815387383479602530349 1179305770268804850948881)
                ·
                  refine ⟨884479327701603638211661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1179305770268804850948881 884479327701603638211661)
                  ·
                    refine ⟨331679747888101364329373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 884479327701603638211661 331679747888101364329373)
                    ·
                      refine ⟨124379905458038011623515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 331679747888101364329373 124379905458038011623515)
                      ·
                        rfl

theorem cell23_242229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_242229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242229 prefixEnd_242229 := by exact prefixLift 242229
  have htrace : WordTrace (prefixWord ++ tailWord_242229) baseStart_242229 baseEnd_242229 := by
    simpa [prefixWord, tailWord_242229, baseEnd_242229] using wordTrace_append hprefix tailTrace_242229
  have hstable : (prefixWord ++ tailWord_242229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242229).length < 2 ^ (prefixWord ++ tailWord_242229).sum := by decide
  have hdescent : baseEnd_242229 < baseStart_242229 := by decide
  rcases family_descends (prefixWord ++ tailWord_242229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242230 : List Nat := [5, 1, 2, 1, 2, 3, 1, 1, 1, 4, 2]
def baseStart_242230 : Nat := 118140960795 + 242230 * 2 ^ 59
def prefixEnd_242230 : Nat := 4983230072969 + 3 ^ 40 * 242230 * 2
def baseEnd_242230 : Nat := 124380418938692507711011

theorem tailTrace_242230 : CollatzResearch.WordTrace tailWord_242230 prefixEnd_242230 124380418938692507711011 := by
  unfold tailWord_242230
  simp only [CollatzResearch.WordTrace]
  refine ⟨552178369528097152219259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5889902608299702957005429 552178369528097152219259)
  ·
    refine ⟨828267554292145728328889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 552178369528097152219259 828267554292145728328889)
    ·
      refine ⟨621200665719109296246667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 828267554292145728328889 621200665719109296246667)
      ·
        refine ⟨931800998578663944370001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621200665719109296246667 931800998578663944370001)
        ·
          refine ⟨698850748933997958277501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 931800998578663944370001 698850748933997958277501)
          ·
            refine ⟨262069030850249234354063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 698850748933997958277501 262069030850249234354063)
            ·
              refine ⟨393103546275373851531095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262069030850249234354063 393103546275373851531095)
              ·
                refine ⟨589655319413060777296643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 393103546275373851531095 589655319413060777296643)
                ·
                  refine ⟨884482979119591165944965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 589655319413060777296643 884482979119591165944965)
                  ·
                    refine ⟨165840558584923343614681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 884482979119591165944965 165840558584923343614681)
                    ·
                      refine ⟨124380418938692507711011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 165840558584923343614681 124380418938692507711011)
                      ·
                        rfl

theorem cell23_242230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_242230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242230 prefixEnd_242230 := by exact prefixLift 242230
  have htrace : WordTrace (prefixWord ++ tailWord_242230) baseStart_242230 baseEnd_242230 := by
    simpa [prefixWord, tailWord_242230, baseEnd_242230] using wordTrace_append hprefix tailTrace_242230
  have hstable : (prefixWord ++ tailWord_242230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242230).length < 2 ^ (prefixWord ++ tailWord_242230).sum := by decide
  have hdescent : baseEnd_242230 < baseStart_242230 := by decide
  rcases family_descends (prefixWord ++ tailWord_242230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242232 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 3, 7]
def baseStart_242232 : Nat := 118140960795 + 242232 * 2 ^ 59
def prefixEnd_242232 : Nat := 4983230072969 + 3 ^ 40 * 242232 * 2
def baseEnd_242232 : Nat := 41460481966667166628667

theorem tailTrace_242232 : CollatzResearch.WordTrace tailWord_242232 prefixEnd_242232 41460481966667166628667 := by
  unfold tailWord_242232
  simp only [CollatzResearch.WordTrace]
  refine ⟨4417463429221154388540475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5889951238961539184720633 4417463429221154388540475)
  ·
    refine ⟨6626195143831731582810713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4417463429221154388540475 6626195143831731582810713)
    ·
      refine ⟨4969646357873798687108035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6626195143831731582810713 4969646357873798687108035)
      ·
        refine ⟨7454469536810698030662053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4969646357873798687108035 7454469536810698030662053)
        ·
          refine ⟨1397713038152005880749135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7454469536810698030662053 1397713038152005880749135)
          ·
            refine ⟨2096569557228008821123703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1397713038152005880749135 2096569557228008821123703)
            ·
              refine ⟨3144854335842013231685555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2096569557228008821123703 3144854335842013231685555)
              ·
                refine ⟨4717281503763019847528333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3144854335842013231685555 4717281503763019847528333)
                ·
                  refine ⟨1768980563911132442823125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4717281503763019847528333 1768980563911132442823125)
                  ·
                    refine ⟨41460481966667166628667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1768980563911132442823125 41460481966667166628667)
                    ·
                      rfl

theorem cell23_242232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 3, 7].length) (baseStart_242232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242232 prefixEnd_242232 := by exact prefixLift 242232
  have htrace : WordTrace (prefixWord ++ tailWord_242232) baseStart_242232 baseEnd_242232 := by
    simpa [prefixWord, tailWord_242232, baseEnd_242232] using wordTrace_append hprefix tailTrace_242232
  have hstable : (prefixWord ++ tailWord_242232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242232).length < 2 ^ (prefixWord ++ tailWord_242232).sum := by decide
  have hdescent : baseEnd_242232 < baseStart_242232 := by decide
  rcases family_descends (prefixWord ++ tailWord_242232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242253 : List Nat := [1, 6, 1, 1, 2, 1, 3, 3, 5]
def baseStart_242253 : Nat := 118140960795 + 242253 * 2 ^ 59
def prefixEnd_242253 : Nat := 4983230072969 + 3 ^ 40 * 242253 * 2
def baseEnd_242253 : Nat := 13821358777082879747045

theorem tailTrace_242253 : CollatzResearch.WordTrace tailWord_242253 prefixEnd_242253 13821358777082879747045 := by
  unfold tailWord_242253
  simp only [CollatzResearch.WordTrace]
  refine ⟨8835692791366229363595413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5890461860910819575730275 8835692791366229363595413)
  ·
    refine ⟨414173099595292001418535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8835692791366229363595413 414173099595292001418535)
    ·
      refine ⟨621259649392938002127803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414173099595292001418535 621259649392938002127803)
      ·
        refine ⟨931889474089407003191705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621259649392938002127803 931889474089407003191705)
        ·
          refine ⟨698917105567055252393779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 931889474089407003191705 698917105567055252393779)
          ·
            refine ⟨1048375658350582878590669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 698917105567055252393779 1048375658350582878590669)
            ·
              refine ⟨393140871881468579471501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1048375658350582878590669 393140871881468579471501)
              ·
                refine ⟨147427826955550717301813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 393140871881468579471501 147427826955550717301813)
                ·
                  refine ⟨13821358777082879747045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 147427826955550717301813 13821358777082879747045)
                  ·
                    rfl

theorem cell23_242253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_242253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242253 prefixEnd_242253 := by exact prefixLift 242253
  have htrace : WordTrace (prefixWord ++ tailWord_242253) baseStart_242253 baseEnd_242253 := by
    simpa [prefixWord, tailWord_242253, baseEnd_242253] using wordTrace_append hprefix tailTrace_242253
  have hstable : (prefixWord ++ tailWord_242253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242253).length < 2 ^ (prefixWord ++ tailWord_242253).sum := by decide
  have hdescent : baseEnd_242253 < baseStart_242253 := by decide
  rcases family_descends (prefixWord ++ tailWord_242253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242403 : List Nat := [1, 1, 1, 7, 1, 3, 1, 1, 1, 6]
def baseStart_242403 : Nat := 118140960795 + 242403 * 2 ^ 59
def prefixEnd_242403 : Nat := 4983230072969 + 3 ^ 40 * 242403 * 2
def baseEnd_242403 : Nat := 41489750363973443615905

theorem tailTrace_242403 : CollatzResearch.WordTrace tailWord_242403 prefixEnd_242403 41489750363973443615905 := by
  unfold tailWord_242403
  simp only [CollatzResearch.WordTrace]
  refine ⟨8841163740822804981555863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5894109160548536654370575 8841163740822804981555863)
  ·
    refine ⟨13261745611234207472333795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8841163740822804981555863 13261745611234207472333795)
    ·
      refine ⟨19892618416851311208500693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13261745611234207472333795 19892618416851311208500693)
      ·
        refine ⟨466233244144952606449235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 19892618416851311208500693 466233244144952606449235)
        ·
          refine ⟨699349866217428909673853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466233244144952606449235 699349866217428909673853)
          ·
            refine ⟨262256199831535841127695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 699349866217428909673853 262256199831535841127695)
            ·
              refine ⟨393384299747303761691543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262256199831535841127695 393384299747303761691543)
              ·
                refine ⟨590076449620955642537315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 393384299747303761691543 590076449620955642537315)
                ·
                  refine ⟨885114674431433463805973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 590076449620955642537315 885114674431433463805973)
                  ·
                    refine ⟨41489750363973443615905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 885114674431433463805973 41489750363973443615905)
                    ·
                      rfl

theorem cell23_242403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 6].length) (baseStart_242403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242403 prefixEnd_242403 := by exact prefixLift 242403
  have htrace : WordTrace (prefixWord ++ tailWord_242403) baseStart_242403 baseEnd_242403 := by
    simpa [prefixWord, tailWord_242403, baseEnd_242403] using wordTrace_append hprefix tailTrace_242403
  have hstable : (prefixWord ++ tailWord_242403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242403).length < 2 ^ (prefixWord ++ tailWord_242403).sum := by decide
  have hdescent : baseEnd_242403 < baseStart_242403 := by decide
  rcases family_descends (prefixWord ++ tailWord_242403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242426 : List Nat := [3, 1, 1, 1, 1, 3, 2, 4, 1, 3, 3]
def baseStart_242426 : Nat := 118140960795 + 242426 * 2 ^ 59
def prefixEnd_242426 : Nat := 4983230072969 + 3 ^ 40 * 242426 * 2
def baseEnd_242426 : Nat := 124481061146973740860109

theorem tailTrace_242426 : CollatzResearch.WordTrace tailWord_242426 prefixEnd_242426 124481061146973740860109 := by
  unfold tailWord_242426
  simp only [CollatzResearch.WordTrace]
  refine ⟨2210500654934869977410783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5894668413159653273095421 2210500654934869977410783)
  ·
    refine ⟨3315750982402304966116175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2210500654934869977410783 3315750982402304966116175)
    ·
      refine ⟨4973626473603457449174263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3315750982402304966116175 4973626473603457449174263)
      ·
        refine ⟨7460439710405186173761395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4973626473603457449174263 7460439710405186173761395)
        ·
          refine ⟨11190659565607779260642093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7460439710405186173761395 11190659565607779260642093)
          ·
            refine ⟨4196497337102917222740785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11190659565607779260642093 4196497337102917222740785)
            ·
              refine ⟨3147373002827187917055589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4196497337102917222740785 3147373002827187917055589)
              ·
                refine ⟨590132438030097734447923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3147373002827187917055589 590132438030097734447923)
                ·
                  refine ⟨885198657045146601671885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 590132438030097734447923 885198657045146601671885)
                  ·
                    refine ⟨331949496391929975626957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 885198657045146601671885 331949496391929975626957)
                    ·
                      refine ⟨124481061146973740860109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 331949496391929975626957 124481061146973740860109)
                      ·
                        rfl

theorem cell23_242426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 1, 3, 3].length) (baseStart_242426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242426 prefixEnd_242426 := by exact prefixLift 242426
  have htrace : WordTrace (prefixWord ++ tailWord_242426) baseStart_242426 baseEnd_242426 := by
    simpa [prefixWord, tailWord_242426, baseEnd_242426] using wordTrace_append hprefix tailTrace_242426
  have hstable : (prefixWord ++ tailWord_242426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242426).length < 2 ^ (prefixWord ++ tailWord_242426).sum := by decide
  have hdescent : baseEnd_242426 < baseStart_242426 := by decide
  rcases family_descends (prefixWord ++ tailWord_242426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242430 : List Nat := [4, 2, 2, 1, 2, 1, 2, 3, 1, 2, 3]
def baseStart_242430 : Nat := 118140960795 + 242430 * 2 ^ 59
def prefixEnd_242430 : Nat := 4983230072969 + 3 ^ 40 * 242430 * 2
def baseEnd_242430 : Nat := 124483115069591725210091

theorem tailTrace_242430 : CollatzResearch.WordTrace tailWord_242430 prefixEnd_242430 124483115069591725210091 := by
  unfold tailWord_242430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1105268563965623574098593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5894765674483325728525829 1105268563965623574098593)
  ·
    refine ⟨828951422974217680573945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1105268563965623574098593 828951422974217680573945)
    ·
      refine ⟨621713567230663260430459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 828951422974217680573945 621713567230663260430459)
      ·
        refine ⟨932570350845994890645689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621713567230663260430459 932570350845994890645689)
        ·
          refine ⟨699427763134496167984267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 932570350845994890645689 699427763134496167984267)
          ·
            refine ⟨1049141644701744251976401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699427763134496167984267 1049141644701744251976401)
            ·
              refine ⟨786856233526308188982301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1049141644701744251976401 786856233526308188982301)
              ·
                refine ⟨295071087572365570868363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 786856233526308188982301 295071087572365570868363)
                ·
                  refine ⟨442606631358548356302545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 295071087572365570868363 442606631358548356302545)
                  ·
                    refine ⟨331954973518911267226909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 442606631358548356302545 331954973518911267226909)
                    ·
                      refine ⟨124483115069591725210091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 331954973518911267226909 124483115069591725210091)
                      ·
                        rfl

theorem cell23_242430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_242430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242430 prefixEnd_242430 := by exact prefixLift 242430
  have htrace : WordTrace (prefixWord ++ tailWord_242430) baseStart_242430 baseEnd_242430 := by
    simpa [prefixWord, tailWord_242430, baseEnd_242430] using wordTrace_append hprefix tailTrace_242430
  have hstable : (prefixWord ++ tailWord_242430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242430).length < 2 ^ (prefixWord ++ tailWord_242430).sum := by decide
  have hdescent : baseEnd_242430 < baseStart_242430 := by decide
  rcases family_descends (prefixWord ++ tailWord_242430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242443 : List Nat := [1, 1, 1, 1, 5, 1, 1, 6, 2, 1, 3]
def baseStart_242443 : Nat := 118140960795 + 242443 * 2 ^ 59
def prefixEnd_242443 : Nat := 4983230072969 + 3 ^ 40 * 242443 * 2
def baseEnd_242443 : Nat := 124489790318100174347531

theorem tailTrace_242443 : CollatzResearch.WordTrace tailWord_242443 prefixEnd_242443 124489790318100174347531 := by
  unfold tailWord_242443
  simp only [CollatzResearch.WordTrace]
  refine ⟨8842622660677891813011983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5895081773785261208674655 8842622660677891813011983)
  ·
    refine ⟨13263933991016837719517975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8842622660677891813011983 13263933991016837719517975)
    ·
      refine ⟨19895900986525256579276963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13263933991016837719517975 19895900986525256579276963)
      ·
        refine ⟨29843851479787884868915445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19895900986525256579276963 29843851479787884868915445)
        ·
          refine ⟨2797861076230114206460823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29843851479787884868915445 2797861076230114206460823)
          ·
            refine ⟨4196791614345171309691235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2797861076230114206460823 4196791614345171309691235)
            ·
              refine ⟨6295187421517756964536853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4196791614345171309691235 6295187421517756964536853)
              ·
                refine ⟨295086910383644857712665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6295187421517756964536853 295086910383644857712665)
                ·
                  refine ⟨221315182787733643284499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 295086910383644857712665 221315182787733643284499)
                  ·
                    refine ⟨331972774181600464926749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 221315182787733643284499 331972774181600464926749)
                    ·
                      refine ⟨124489790318100174347531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 331972774181600464926749 124489790318100174347531)
                      ·
                        rfl

theorem cell23_242443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6, 2, 1, 3].length) (baseStart_242443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242443 prefixEnd_242443 := by exact prefixLift 242443
  have htrace : WordTrace (prefixWord ++ tailWord_242443) baseStart_242443 baseEnd_242443 := by
    simpa [prefixWord, tailWord_242443, baseEnd_242443] using wordTrace_append hprefix tailTrace_242443
  have hstable : (prefixWord ++ tailWord_242443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242443).length < 2 ^ (prefixWord ++ tailWord_242443).sum := by decide
  have hdescent : baseEnd_242443 < baseStart_242443 := by decide
  rcases family_descends (prefixWord ++ tailWord_242443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242453 : List Nat := [1, 3, 2, 1, 2, 2, 2, 2, 3, 3, 2]
def baseStart_242453 : Nat := 118140960795 + 242453 * 2 ^ 59
def prefixEnd_242453 : Nat := 4983230072969 + 3 ^ 40 * 242453 * 2
def baseEnd_242453 : Nat := 124494925124645135222485

theorem tailTrace_242453 : CollatzResearch.WordTrace tailWord_242453 prefixEnd_242453 124494925124645135222485 := by
  unfold tailWord_242453
  simp only [CollatzResearch.WordTrace]
  refine ⟨8842987390641663520876013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5895324927094442347250675 8842987390641663520876013)
  ·
    refine ⟨3316120271490623820328505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8842987390641663520876013 3316120271490623820328505)
    ·
      refine ⟨2487090203617967865246379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3316120271490623820328505 2487090203617967865246379)
      ·
        refine ⟨3730635305426951797869569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2487090203617967865246379 3730635305426951797869569)
        ·
          refine ⟨2797976479070213848402177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3730635305426951797869569 2797976479070213848402177)
          ·
            refine ⟨2098482359302660386301633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2797976479070213848402177 2098482359302660386301633)
            ·
              refine ⟨1573861769476995289726225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2098482359302660386301633 1573861769476995289726225)
              ·
                refine ⟨1180396327107746467294669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1573861769476995289726225 1180396327107746467294669)
                ·
                  refine ⟨442648622665404925235501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1180396327107746467294669 442648622665404925235501)
                  ·
                    refine ⟨165993233499526846963313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 442648622665404925235501 165993233499526846963313)
                    ·
                      refine ⟨124494925124645135222485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 165993233499526846963313 124494925124645135222485)
                      ·
                        rfl

theorem cell23_242453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3, 3, 2].length) (baseStart_242453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242453 prefixEnd_242453 := by exact prefixLift 242453
  have htrace : WordTrace (prefixWord ++ tailWord_242453) baseStart_242453 baseEnd_242453 := by
    simpa [prefixWord, tailWord_242453, baseEnd_242453] using wordTrace_append hprefix tailTrace_242453
  have hstable : (prefixWord ++ tailWord_242453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242453).length < 2 ^ (prefixWord ++ tailWord_242453).sum := by decide
  have hdescent : baseEnd_242453 < baseStart_242453 := by decide
  rcases family_descends (prefixWord ++ tailWord_242453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242460 : List Nat := [2, 2, 3, 1, 1, 4, 1, 3, 2, 1, 3]
def baseStart_242460 : Nat := 118140960795 + 242460 * 2 ^ 59
def prefixEnd_242460 : Nat := 4983230072969 + 3 ^ 40 * 242460 * 2
def baseEnd_242460 : Nat := 124498519489226607834953

theorem tailTrace_242460 : CollatzResearch.WordTrace tailWord_242460 prefixEnd_242460 124498519489226607834953 := by
  unfold tailWord_242460
  simp only [CollatzResearch.WordTrace]
  refine ⟨4421621350808151858190417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5895495134410869144253889 4421621350808151858190417)
  ·
    refine ⟨3316216013106113893642813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4421621350808151858190417 3316216013106113893642813)
    ·
      refine ⟨1243581004914792710116055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3316216013106113893642813 1243581004914792710116055)
      ·
        refine ⟨1865371507372189065174083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1243581004914792710116055 1865371507372189065174083)
        ·
          refine ⟨2798057261058283597761125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1865371507372189065174083 2798057261058283597761125)
          ·
            refine ⟨524635736448428174580211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2798057261058283597761125 524635736448428174580211)
            ·
              refine ⟨786953604672642261870317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 524635736448428174580211 786953604672642261870317)
              ·
                refine ⟨295107601752240848201369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 786953604672642261870317 295107601752240848201369)
                ·
                  refine ⟨221330701314180636151027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 295107601752240848201369 221330701314180636151027)
                  ·
                    refine ⟨331996051971270954226541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 221330701314180636151027 331996051971270954226541)
                    ·
                      refine ⟨124498519489226607834953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 331996051971270954226541 124498519489226607834953)
                      ·
                        rfl

theorem cell23_242460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_242460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242460 prefixEnd_242460 := by exact prefixLift 242460
  have htrace : WordTrace (prefixWord ++ tailWord_242460) baseStart_242460 baseEnd_242460 := by
    simpa [prefixWord, tailWord_242460, baseEnd_242460] using wordTrace_append hprefix tailTrace_242460
  have hstable : (prefixWord ++ tailWord_242460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242460).length < 2 ^ (prefixWord ++ tailWord_242460).sum := by decide
  have hdescent : baseEnd_242460 < baseStart_242460 := by decide
  rcases family_descends (prefixWord ++ tailWord_242460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242477 : List Nat := [1, 5, 3, 2, 1, 1, 1, 2, 1, 3, 3]
def baseStart_242477 : Nat := 118140960795 + 242477 * 2 ^ 59
def prefixEnd_242477 : Nat := 4983230072969 + 3 ^ 40 * 242477 * 2
def baseEnd_242477 : Nat := 124507248660353041322375

theorem tailTrace_242477 : CollatzResearch.WordTrace tailWord_242477 prefixEnd_242477 124507248660353041322375 := by
  unfold tailWord_242477
  simp only [CollatzResearch.WordTrace]
  refine ⟨8843862742554715619749685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5895908495036477079833123 8843862742554715619749685)
  ·
    refine ⟨829112132114504589351533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8843862742554715619749685 829112132114504589351533)
    ·
      refine ⟨310917049542939221006825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 829112132114504589351533 310917049542939221006825)
      ·
        refine ⟨233187787157204415755119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310917049542939221006825 233187787157204415755119)
        ·
          refine ⟨349781680735806623632679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233187787157204415755119 349781680735806623632679)
          ·
            refine ⟨524672521103709935449019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349781680735806623632679 524672521103709935449019)
            ·
              refine ⟨787008781655564903173529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 524672521103709935449019 787008781655564903173529)
              ·
                refine ⟨590256586241673677380147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 787008781655564903173529 590256586241673677380147)
                ·
                  refine ⟨885384879362510516070221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 590256586241673677380147 885384879362510516070221)
                  ·
                    refine ⟨332019329760941443526333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 885384879362510516070221 332019329760941443526333)
                    ·
                      refine ⟨124507248660353041322375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 332019329760941443526333 124507248660353041322375)
                      ·
                        rfl

theorem cell23_242477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_242477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242477 prefixEnd_242477 := by exact prefixLift 242477
  have htrace : WordTrace (prefixWord ++ tailWord_242477) baseStart_242477 baseEnd_242477 := by
    simpa [prefixWord, tailWord_242477, baseEnd_242477] using wordTrace_append hprefix tailTrace_242477
  have hstable : (prefixWord ++ tailWord_242477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242477).length < 2 ^ (prefixWord ++ tailWord_242477).sum := by decide
  have hdescent : baseEnd_242477 < baseStart_242477 := by decide
  rcases family_descends (prefixWord ++ tailWord_242477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242483 : List Nat := [1, 1, 1, 2, 6, 1, 1, 1, 3, 4, 2]
def baseStart_242483 : Nat := 118140960795 + 242483 * 2 ^ 59
def prefixEnd_242483 : Nat := 4983230072969 + 3 ^ 40 * 242483 * 2
def baseEnd_242483 : Nat := 124510329544280017847347

theorem tailTrace_242483 : CollatzResearch.WordTrace tailWord_242483 prefixEnd_242483 124510329544280017847347 := by
  unfold tailWord_242483
  simp only [CollatzResearch.WordTrace]
  refine ⟨8844081580532978644468103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5896054387021985762978735 8844081580532978644468103)
  ·
    refine ⟨13266122370799467966702155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8844081580532978644468103 13266122370799467966702155)
    ·
      refine ⟨19899183556199201950053233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13266122370799467966702155 19899183556199201950053233)
      ·
        refine ⟨14924387667149401462539925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19899183556199201950053233 14924387667149401462539925)
        ·
          refine ⟨699580671897628193556559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14924387667149401462539925 699580671897628193556559)
          ·
            refine ⟨1049371007846442290334839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699580671897628193556559 1049371007846442290334839)
            ·
              refine ⟨1574056511769663435502259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1049371007846442290334839 1574056511769663435502259)
              ·
                refine ⟨2361084767654495153253389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1574056511769663435502259 2361084767654495153253389)
                ·
                  refine ⟨885406787870435682470021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2361084767654495153253389 885406787870435682470021)
                  ·
                    refine ⟨166013772725706690463129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 885406787870435682470021 166013772725706690463129)
                    ·
                      refine ⟨124510329544280017847347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 166013772725706690463129 124510329544280017847347)
                      ·
                        rfl

theorem cell23_242483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 4, 2].length) (baseStart_242483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242483 prefixEnd_242483 := by exact prefixLift 242483
  have htrace : WordTrace (prefixWord ++ tailWord_242483) baseStart_242483 baseEnd_242483 := by
    simpa [prefixWord, tailWord_242483, baseEnd_242483] using wordTrace_append hprefix tailTrace_242483
  have hstable : (prefixWord ++ tailWord_242483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242483).length < 2 ^ (prefixWord ++ tailWord_242483).sum := by decide
  have hdescent : baseEnd_242483 < baseStart_242483 := by decide
  rcases family_descends (prefixWord ++ tailWord_242483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242513 : List Nat := [1, 2, 2, 1, 6, 1, 1, 1, 2, 2, 4]
def baseStart_242513 : Nat := 118140960795 + 242513 * 2 ^ 59
def prefixEnd_242513 : Nat := 4983230072969 + 3 ^ 40 * 242513 * 2
def baseEnd_242513 : Nat := 124525733963914900472209

theorem tailTrace_242513 : CollatzResearch.WordTrace tailWord_242513 prefixEnd_242513 124525733963914900472209 := by
  unfold tailWord_242513
  simp only [CollatzResearch.WordTrace]
  refine ⟨8845175770424293768060193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5896783846949529178706795 8845175770424293768060193)
  ·
    refine ⟨6633881827818220326045145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8845175770424293768060193 6633881827818220326045145)
    ·
      refine ⟨4975411370863665244533859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6633881827818220326045145 4975411370863665244533859)
      ·
        refine ⟨7463117056295497866800789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4975411370863665244533859 7463117056295497866800789)
        ·
          refine ⟨349833612013851462506287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7463117056295497866800789 349833612013851462506287)
          ·
            refine ⟨524750418020777193759431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349833612013851462506287 524750418020777193759431)
            ·
              refine ⟨787125627031165790639147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 524750418020777193759431 787125627031165790639147)
              ·
                refine ⟨1180688440546748685958721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 787125627031165790639147 1180688440546748685958721)
                ·
                  refine ⟨885516330410061514469041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1180688440546748685958721 885516330410061514469041)
                  ·
                    refine ⟨664137247807546135851781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 885516330410061514469041 664137247807546135851781)
                    ·
                      refine ⟨124525733963914900472209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 664137247807546135851781 124525733963914900472209)
                      ·
                        rfl

theorem cell23_242513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 2, 4].length) (baseStart_242513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242513 prefixEnd_242513 := by exact prefixLift 242513
  have htrace : WordTrace (prefixWord ++ tailWord_242513) baseStart_242513 baseEnd_242513 := by
    simpa [prefixWord, tailWord_242513, baseEnd_242513] using wordTrace_append hprefix tailTrace_242513
  have hstable : (prefixWord ++ tailWord_242513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242513).length < 2 ^ (prefixWord ++ tailWord_242513).sum := by decide
  have hdescent : baseEnd_242513 < baseStart_242513 := by decide
  rcases family_descends (prefixWord ++ tailWord_242513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242546 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 3, 2, 5]
def baseStart_242546 : Nat := 118140960795 + 242546 * 2 ^ 59
def prefixEnd_242546 : Nat := 4983230072969 + 3 ^ 40 * 242546 * 2
def baseEnd_242546 : Nat := 124542678825513271359557

theorem tailTrace_242546 : CollatzResearch.WordTrace tailWord_242546 prefixEnd_242546 124542678825513271359557 := by
  unfold tailWord_242546
  simp only [CollatzResearch.WordTrace]
  refine ⟨2211594844826185101002873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5897586252869826936007661 2211594844826185101002873)
  ·
    refine ⟨1658696133619638825752155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2211594844826185101002873 1658696133619638825752155)
    ·
      refine ⟨2488044200429458238628233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1658696133619638825752155 2488044200429458238628233)
      ·
        refine ⟨1866033150322093678971175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2488044200429458238628233 1866033150322093678971175)
        ·
          refine ⟨2799049725483140518456763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1866033150322093678971175 2799049725483140518456763)
          ·
            refine ⟨4198574588224710777685145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2799049725483140518456763 4198574588224710777685145)
            ·
              refine ⟨3148930941168533083263859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4198574588224710777685145 3148930941168533083263859)
              ·
                refine ⟨4723396411752799624895789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3148930941168533083263859 4723396411752799624895789)
                ·
                  refine ⟨1771273654407299859335921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4723396411752799624895789 1771273654407299859335921)
                  ·
                    refine ⟨1328455240805474894501941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1771273654407299859335921 1328455240805474894501941)
                    ·
                      refine ⟨124542678825513271359557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1328455240805474894501941 124542678825513271359557)
                      ·
                        rfl

theorem cell23_242546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_242546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242546 prefixEnd_242546 := by exact prefixLift 242546
  have htrace : WordTrace (prefixWord ++ tailWord_242546) baseStart_242546 baseEnd_242546 := by
    simpa [prefixWord, tailWord_242546, baseEnd_242546] using wordTrace_append hprefix tailTrace_242546
  have hstable : (prefixWord ++ tailWord_242546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242546).length < 2 ^ (prefixWord ++ tailWord_242546).sum := by decide
  have hdescent : baseEnd_242546 < baseStart_242546 := by decide
  rcases family_descends (prefixWord ++ tailWord_242546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242550 : List Nat := [5, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3]
def baseStart_242550 : Nat := 118140960795 + 242550 * 2 ^ 59
def prefixEnd_242550 : Nat := 4983230072969 + 3 ^ 40 * 242550 * 2
def baseEnd_242550 : Nat := 124544732748131255709539

theorem tailTrace_242550 : CollatzResearch.WordTrace tailWord_242550 prefixEnd_242550 124544732748131255709539 := by
  unfold tailWord_242550
  simp only [CollatzResearch.WordTrace]
  refine ⟨552907829455640567947319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5897683514193499391438069 552907829455640567947319)
  ·
    refine ⟨829361744183460851920979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 552907829455640567947319 829361744183460851920979)
    ·
      refine ⟨1244042616275191277881469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 829361744183460851920979 1244042616275191277881469)
      ·
        refine ⟨466515981103196729205551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1244042616275191277881469 466515981103196729205551)
        ·
          refine ⟨699773971654795093808327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466515981103196729205551 699773971654795093808327)
          ·
            refine ⟨1049660957482192640712491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699773971654795093808327 1049660957482192640712491)
            ·
              refine ⟨1574491436223288961068737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1049660957482192640712491 1574491436223288961068737)
              ·
                refine ⟨1180868577167466720801553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1574491436223288961068737 1180868577167466720801553)
                ·
                  refine ⟨885651432875600040601165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1180868577167466720801553 885651432875600040601165)
                  ·
                    refine ⟨332119287328350015225437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 885651432875600040601165 332119287328350015225437)
                    ·
                      refine ⟨124544732748131255709539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 332119287328350015225437 124544732748131255709539)
                      ·
                        rfl

theorem cell23_242550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_242550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242550 prefixEnd_242550 := by exact prefixLift 242550
  have htrace : WordTrace (prefixWord ++ tailWord_242550) baseStart_242550 baseEnd_242550 := by
    simpa [prefixWord, tailWord_242550, baseEnd_242550] using wordTrace_append hprefix tailTrace_242550
  have hstable : (prefixWord ++ tailWord_242550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242550).length < 2 ^ (prefixWord ++ tailWord_242550).sum := by decide
  have hdescent : baseEnd_242550 < baseStart_242550 := by decide
  rcases family_descends (prefixWord ++ tailWord_242550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242583 : List Nat := [1, 1, 3, 3, 1, 2, 1, 4, 3, 4]
def baseStart_242583 : Nat := 118140960795 + 242583 * 2 ^ 59
def prefixEnd_242583 : Nat := 4983230072969 + 3 ^ 40 * 242583 * 2
def baseEnd_242583 : Nat := 41520559203243208865629

theorem tailTrace_242583 : CollatzResearch.WordTrace tailWord_242583 prefixEnd_242583 41520559203243208865629 := by
  unfold tailWord_242583
  simp only [CollatzResearch.WordTrace]
  refine ⟨8847728880170695723108403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5898485920113797148738935 8847728880170695723108403)
  ·
    refine ⟨13271593320256043584662605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8847728880170695723108403 13271593320256043584662605)
    ·
      refine ⟨4976847495096016344248477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13271593320256043584662605 4976847495096016344248477)
      ·
        refine ⟨1866317810661006129093179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4976847495096016344248477 1866317810661006129093179)
        ·
          refine ⟨2799476715991509193639769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1866317810661006129093179 2799476715991509193639769)
          ·
            refine ⟨2099607536993631895229827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2799476715991509193639769 2099607536993631895229827)
            ·
              refine ⟨3149411305490447842844741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2099607536993631895229827 3149411305490447842844741)
              ·
                refine ⟨590514619779458970533389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3149411305490447842844741 590514619779458970533389)
                ·
                  refine ⟨221442982417297113950021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 590514619779458970533389 221442982417297113950021)
                  ·
                    refine ⟨41520559203243208865629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 221442982417297113950021 41520559203243208865629)
                    ·
                      rfl

theorem cell23_242583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 3, 4].length) (baseStart_242583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242583 prefixEnd_242583 := by exact prefixLift 242583
  have htrace : WordTrace (prefixWord ++ tailWord_242583) baseStart_242583 baseEnd_242583 := by
    simpa [prefixWord, tailWord_242583, baseEnd_242583] using wordTrace_append hprefix tailTrace_242583
  have hstable : (prefixWord ++ tailWord_242583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242583).length < 2 ^ (prefixWord ++ tailWord_242583).sum := by decide
  have hdescent : baseEnd_242583 < baseStart_242583 := by decide
  rcases family_descends (prefixWord ++ tailWord_242583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242596 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 10]
def baseStart_242596 : Nat := 118140960795 + 242596 * 2 ^ 59
def prefixEnd_242596 : Nat := 4983230072969 + 3 ^ 40 * 242596 * 2
def baseEnd_242596 : Nat := 13840928095359786192703

theorem tailTrace_242596 : CollatzResearch.WordTrace tailWord_242596 prefixEnd_242596 13840928095359786192703 := by
  unfold tailWord_242596
  simp only [CollatzResearch.WordTrace]
  refine ⟨4424101514561799471665821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5898802019415732628887761 4424101514561799471665821)
  ·
    refine ⟨1659038067960674801874683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4424101514561799471665821 1659038067960674801874683)
    ·
      refine ⟨2488557101941012202812025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1659038067960674801874683 2488557101941012202812025)
      ·
        refine ⟨1866417826455759152109019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2488557101941012202812025 1866417826455759152109019)
        ·
          refine ⟨2799626739683638728163529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1866417826455759152109019 2799626739683638728163529)
          ·
            refine ⟨2099720054762729046122647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2799626739683638728163529 2099720054762729046122647)
            ·
              refine ⟨3149580082144093569183971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2099720054762729046122647 3149580082144093569183971)
              ·
                refine ⟨4724370123216140353775957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3149580082144093569183971 4724370123216140353775957)
                ·
                  refine ⟨13840928095359786192703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 4724370123216140353775957 13840928095359786192703)
                  ·
                    rfl

theorem cell23_242596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 10].length) (baseStart_242596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242596 prefixEnd_242596 := by exact prefixLift 242596
  have htrace : WordTrace (prefixWord ++ tailWord_242596) baseStart_242596 baseEnd_242596 := by
    simpa [prefixWord, tailWord_242596, baseEnd_242596] using wordTrace_append hprefix tailTrace_242596
  have hstable : (prefixWord ++ tailWord_242596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242596).length < 2 ^ (prefixWord ++ tailWord_242596).sum := by decide
  have hdescent : baseEnd_242596 < baseStart_242596 := by decide
  rcases family_descends (prefixWord ++ tailWord_242596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242613 : List Nat := [1, 3, 3, 2, 1, 1, 2, 4, 6]
def baseStart_242613 : Nat := 118140960795 + 242613 * 2 ^ 59
def prefixEnd_242613 : Nat := 4983230072969 + 3 ^ 40 * 242613 * 2
def baseEnd_242613 : Nat := 13841898003262723246861

theorem tailTrace_242613 : CollatzResearch.WordTrace tailWord_242613 prefixEnd_242613 13841898003262723246861 := by
  unfold tailWord_242613
  simp only [CollatzResearch.WordTrace]
  refine ⟨8848823070062010846700493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5899215380041340564466995 8848823070062010846700493)
  ·
    refine ⟨3318308651273254067512685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8848823070062010846700493 3318308651273254067512685)
    ·
      refine ⟨1244365744227470275317257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3318308651273254067512685 1244365744227470275317257)
      ·
        refine ⟨933274308170602706487943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1244365744227470275317257 933274308170602706487943)
        ·
          refine ⟨1399911462255904059731915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 933274308170602706487943 1399911462255904059731915)
          ·
            refine ⟨2099867193383856089597873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1399911462255904059731915 2099867193383856089597873)
            ·
              refine ⟨1574900395037892067198405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2099867193383856089597873 1574900395037892067198405)
              ·
                refine ⟨295293824069604762599701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1574900395037892067198405 295293824069604762599701)
                ·
                  refine ⟨13841898003262723246861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 295293824069604762599701 13841898003262723246861)
                  ·
                    rfl

theorem cell23_242613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4, 6].length) (baseStart_242613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242613 prefixEnd_242613 := by exact prefixLift 242613
  have htrace : WordTrace (prefixWord ++ tailWord_242613) baseStart_242613 baseEnd_242613 := by
    simpa [prefixWord, tailWord_242613, baseEnd_242613] using wordTrace_append hprefix tailTrace_242613
  have hstable : (prefixWord ++ tailWord_242613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242613).length < 2 ^ (prefixWord ++ tailWord_242613).sum := by decide
  have hdescent : baseEnd_242613 < baseStart_242613 := by decide
  rcases family_descends (prefixWord ++ tailWord_242613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242614 : List Nat := [5, 1, 4, 1, 1, 1, 1, 1, 1, 2, 5]
def baseStart_242614 : Nat := 118140960795 + 242614 * 2 ^ 59
def prefixEnd_242614 : Nat := 4983230072969 + 3 ^ 40 * 242614 * 2
def baseEnd_242614 : Nat := 124577595510019005309245

theorem tailTrace_242614 : CollatzResearch.WordTrace tailWord_242614 prefixEnd_242614 124577595510019005309245 := by
  unfold tailWord_242614
  simp only [CollatzResearch.WordTrace]
  refine ⟨553053721441149251092931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5899239695372258678324597 553053721441149251092931)
  ·
    refine ⟨829580582161723876639397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 553053721441149251092931 829580582161723876639397)
    ·
      refine ⟨155546359155323226869887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 829580582161723876639397 155546359155323226869887)
      ·
        refine ⟨233319538732984840304831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155546359155323226869887 233319538732984840304831)
        ·
          refine ⟨349979308099477260457247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233319538732984840304831 349979308099477260457247)
          ·
            refine ⟨524968962149215890685871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349979308099477260457247 524968962149215890685871)
            ·
              refine ⟨787453443223823836028807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 524968962149215890685871 787453443223823836028807)
              ·
                refine ⟨1181180164835735754043211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 787453443223823836028807 1181180164835735754043211)
                ·
                  refine ⟨1771770247253603631064817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1181180164835735754043211 1771770247253603631064817)
                  ·
                    refine ⟨1328827685440202723298613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1771770247253603631064817 1328827685440202723298613)
                    ·
                      refine ⟨124577595510019005309245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1328827685440202723298613 124577595510019005309245)
                      ·
                        rfl

theorem cell23_242614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_242614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242614 prefixEnd_242614 := by exact prefixLift 242614
  have htrace : WordTrace (prefixWord ++ tailWord_242614) baseStart_242614 baseEnd_242614 := by
    simpa [prefixWord, tailWord_242614, baseEnd_242614] using wordTrace_append hprefix tailTrace_242614
  have hstable : (prefixWord ++ tailWord_242614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242614).length < 2 ^ (prefixWord ++ tailWord_242614).sum := by decide
  have hdescent : baseEnd_242614 < baseStart_242614 := by decide
  rcases family_descends (prefixWord ++ tailWord_242614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242657 : List Nat := [1, 2, 3, 1, 2, 1, 1, 7, 1, 1, 3]
def baseStart_242657 : Nat := 118140960795 + 242657 * 2 ^ 59
def prefixEnd_242657 : Nat := 4983230072969 + 3 ^ 40 * 242657 * 2
def baseEnd_242657 : Nat := 124599675178162337071547

theorem tailTrace_242657 : CollatzResearch.WordTrace tailWord_242657 prefixEnd_242657 124599675178162337071547 := by
  unfold tailWord_242657
  simp only [CollatzResearch.WordTrace]
  refine ⟨8850427881902606361302225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5900285254601737574201483 8850427881902606361302225)
  ·
    refine ⟨6637820911426954770976669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8850427881902606361302225 6637820911426954770976669)
    ·
      refine ⟨2489182841785108039116251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6637820911426954770976669 2489182841785108039116251)
      ·
        refine ⟨3733774262677662058674377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2489182841785108039116251 3733774262677662058674377)
        ·
          refine ⟨2800330697008246544005783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3733774262677662058674377 2800330697008246544005783)
          ·
            refine ⟨4200496045512369816008675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2800330697008246544005783 4200496045512369816008675)
            ·
              refine ⟨6300744068268554724013013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4200496045512369816008675 6300744068268554724013013)
              ·
                refine ⟨147673689100044251344055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6300744068268554724013013 147673689100044251344055)
                ·
                  refine ⟨221510533650066377016083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147673689100044251344055 221510533650066377016083)
                  ·
                    refine ⟨332265800475099565524125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 221510533650066377016083 332265800475099565524125)
                    ·
                      refine ⟨124599675178162337071547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 332265800475099565524125 124599675178162337071547)
                      ·
                        rfl

theorem cell23_242657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 7, 1, 1, 3].length) (baseStart_242657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242657 prefixEnd_242657 := by exact prefixLift 242657
  have htrace : WordTrace (prefixWord ++ tailWord_242657) baseStart_242657 baseEnd_242657 := by
    simpa [prefixWord, tailWord_242657, baseEnd_242657] using wordTrace_append hprefix tailTrace_242657
  have hstable : (prefixWord ++ tailWord_242657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242657).length < 2 ^ (prefixWord ++ tailWord_242657).sum := by decide
  have hdescent : baseEnd_242657 < baseStart_242657 := by decide
  rcases family_descends (prefixWord ++ tailWord_242657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242700 : List Nat := [2, 2, 1, 2, 3, 2, 2, 1, 3, 2, 3]
def baseStart_242700 : Nat := 118140960795 + 242700 * 2 ^ 59
def prefixEnd_242700 : Nat := 4983230072969 + 3 ^ 40 * 242700 * 2
def baseEnd_242700 : Nat := 124621754846305668833849

theorem tailTrace_242700 : CollatzResearch.WordTrace tailWord_242700 prefixEnd_242700 124621754846305668833849 := by
  unfold tailWord_242700
  simp only [CollatzResearch.WordTrace]
  refine ⟨4425998110373412352558777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5901330813831216470078369 4425998110373412352558777)
  ·
    refine ⟨3319498582780059264419083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4425998110373412352558777 3319498582780059264419083)
    ·
      refine ⟨4979247874170088896628625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3319498582780059264419083 4979247874170088896628625)
      ·
        refine ⟨3734435905627566672471469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4979247874170088896628625 3734435905627566672471469)
        ·
          refine ⟨1400413464610337502176801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3734435905627566672471469 1400413464610337502176801)
          ·
            refine ⟨1050310098457753126632601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1400413464610337502176801 1050310098457753126632601)
            ·
              refine ⟨787732573843314844974451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1050310098457753126632601 787732573843314844974451)
              ·
                refine ⟨1181598860764972267461677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 787732573843314844974451 1181598860764972267461677)
                ·
                  refine ⟨443099572786864600298129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1181598860764972267461677 443099572786864600298129)
                  ·
                    refine ⟨332324679590148450223597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 443099572786864600298129 332324679590148450223597)
                    ·
                      refine ⟨124621754846305668833849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 332324679590148450223597 124621754846305668833849)
                      ·
                        rfl

theorem cell23_242700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 3, 2, 3].length) (baseStart_242700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242700 prefixEnd_242700 := by exact prefixLift 242700
  have htrace : WordTrace (prefixWord ++ tailWord_242700) baseStart_242700 baseEnd_242700 := by
    simpa [prefixWord, tailWord_242700, baseEnd_242700] using wordTrace_append hprefix tailTrace_242700
  have hstable : (prefixWord ++ tailWord_242700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242700).length < 2 ^ (prefixWord ++ tailWord_242700).sum := by decide
  have hdescent : baseEnd_242700 < baseStart_242700 := by decide
  rcases family_descends (prefixWord ++ tailWord_242700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242720 : List Nat := [2, 1, 1, 7, 1, 1, 10]
def baseStart_242720 : Nat := 118140960795 + 242720 * 2 ^ 59
def prefixEnd_242720 : Nat := 4983230072969 + 3 ^ 40 * 242720 * 2
def baseEnd_242720 : Nat := 1538666968634513463997

theorem tailTrace_242720 : CollatzResearch.WordTrace tailWord_242720 prefixEnd_242720 1538666968634513463997 := by
  unfold tailWord_242720
  simp only [CollatzResearch.WordTrace]
  refine ⟨4426362840337184060422807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5901817120449578747230409 4426362840337184060422807)
  ·
    refine ⟨6639544260505776090634211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4426362840337184060422807 6639544260505776090634211)
    ·
      refine ⟨9959316390758664135951317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6639544260505776090634211 9959316390758664135951317)
      ·
        refine ⟨233421477908406190686359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 9959316390758664135951317 233421477908406190686359)
        ·
          refine ⟨350132216862609286029539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233421477908406190686359 350132216862609286029539)
          ·
            refine ⟨525198325293913929044309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350132216862609286029539 525198325293913929044309)
            ·
              refine ⟨1538666968634513463997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 525198325293913929044309 1538666968634513463997)
              ·
                rfl

theorem cell23_242720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 10].length) (baseStart_242720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242720 prefixEnd_242720 := by exact prefixLift 242720
  have htrace : WordTrace (prefixWord ++ tailWord_242720) baseStart_242720 baseEnd_242720 := by
    simpa [prefixWord, tailWord_242720, baseEnd_242720] using wordTrace_append hprefix tailTrace_242720
  have hstable : (prefixWord ++ tailWord_242720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242720).length < 2 ^ (prefixWord ++ tailWord_242720).sum := by decide
  have hdescent : baseEnd_242720 < baseStart_242720 := by decide
  rcases family_descends (prefixWord ++ tailWord_242720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242724 : List Nat := [2, 3, 1, 4, 1, 3, 1, 2, 2, 4]
def baseStart_242724 : Nat := 118140960795 + 242724 * 2 ^ 59
def prefixEnd_242724 : Nat := 4983230072969 + 3 ^ 40 * 242724 * 2
def baseEnd_242724 : Nat := 41544692794004524977913

theorem tailTrace_242724 : CollatzResearch.WordTrace tailWord_242724 prefixEnd_242724 41544692794004524977913 := by
  unfold tailWord_242724
  simp only [CollatzResearch.WordTrace]
  refine ⟨4426435786329938401995613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5901914381773251202660817 4426435786329938401995613)
  ·
    refine ⟨1659913419873726900748355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4426435786329938401995613 1659913419873726900748355)
    ·
      refine ⟨2489870129810590351122533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1659913419873726900748355 2489870129810590351122533)
      ·
        refine ⟨466850649339485690835475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2489870129810590351122533 466850649339485690835475)
        ·
          refine ⟨700275974009228536253213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466850649339485690835475 700275974009228536253213)
          ·
            refine ⟨262603490253460701094955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 700275974009228536253213 262603490253460701094955)
            ·
              refine ⟨393905235380191051642433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262603490253460701094955 393905235380191051642433)
              ·
                refine ⟨295428926535143288731825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 393905235380191051642433 295428926535143288731825)
                ·
                  refine ⟨221571694901357466548869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 295428926535143288731825 221571694901357466548869)
                  ·
                    refine ⟨41544692794004524977913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 221571694901357466548869 41544692794004524977913)
                    ·
                      rfl

theorem cell23_242724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 2, 2, 4].length) (baseStart_242724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242724 prefixEnd_242724 := by exact prefixLift 242724
  have htrace : WordTrace (prefixWord ++ tailWord_242724) baseStart_242724 baseEnd_242724 := by
    simpa [prefixWord, tailWord_242724, baseEnd_242724] using wordTrace_append hprefix tailTrace_242724
  have hstable : (prefixWord ++ tailWord_242724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242724).length < 2 ^ (prefixWord ++ tailWord_242724).sum := by decide
  have hdescent : baseEnd_242724 < baseStart_242724 := by decide
  rcases family_descends (prefixWord ++ tailWord_242724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242757 : List Nat := [1, 3, 1, 1, 1, 3, 3, 4, 1, 3, 2]
def baseStart_242757 : Nat := 118140960795 + 242757 * 2 ^ 59
def prefixEnd_242757 : Nat := 4983230072969 + 3 ^ 40 * 242757 * 2
def baseEnd_242757 : Nat := 124651023243611945821087

theorem tailTrace_242757 : CollatzResearch.WordTrace tailWord_242757 prefixEnd_242757 124651023243611945821087 := by
  unfold tailWord_242757
  simp only [CollatzResearch.WordTrace]
  refine ⟨8854075181540323439942525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5902716787693548959961683 8854075181540323439942525)
  ·
    refine ⟨3320278193077621289978447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8854075181540323439942525 3320278193077621289978447)
    ·
      refine ⟨4980417289616431934967671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3320278193077621289978447 4980417289616431934967671)
      ·
        refine ⟨7470625934424647902451507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4980417289616431934967671 7470625934424647902451507)
        ·
          refine ⟨11205938901636971853677261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7470625934424647902451507 11205938901636971853677261)
          ·
            refine ⟨4202227088113864445128973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11205938901636971853677261 4202227088113864445128973)
            ·
              refine ⟨1575835158042699166923365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4202227088113864445128973 1575835158042699166923365)
              ·
                refine ⟨295469092133006093798131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1575835158042699166923365 295469092133006093798131)
                ·
                  refine ⟨443203638199509140697197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 295469092133006093798131 443203638199509140697197)
                  ·
                    refine ⟨166201364324815927761449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 443203638199509140697197 166201364324815927761449)
                    ·
                      refine ⟨124651023243611945821087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 166201364324815927761449 124651023243611945821087)
                      ·
                        rfl

theorem cell23_242757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4, 1, 3, 2].length) (baseStart_242757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242757 prefixEnd_242757 := by exact prefixLift 242757
  have htrace : WordTrace (prefixWord ++ tailWord_242757) baseStart_242757 baseEnd_242757 := by
    simpa [prefixWord, tailWord_242757, baseEnd_242757] using wordTrace_append hprefix tailTrace_242757
  have hstable : (prefixWord ++ tailWord_242757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242757).length < 2 ^ (prefixWord ++ tailWord_242757).sum := by decide
  have hdescent : baseEnd_242757 < baseStart_242757 := by decide
  rcases family_descends (prefixWord ++ tailWord_242757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242782 : List Nat := [4, 4, 1, 1, 1, 2, 3, 2, 1, 2, 2]
def baseStart_242782 : Nat := 118140960795 + 242782 * 2 ^ 59
def prefixEnd_242782 : Nat := 4983230072969 + 3 ^ 40 * 242782 * 2
def baseEnd_242782 : Nat := 124663860259974348008473

theorem tailTrace_242782 : CollatzResearch.WordTrace tailWord_242782 prefixEnd_242782 124663860259974348008473 := by
  unfold tailWord_242782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1106873375806219088700325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5903324670966501806401733 1106873375806219088700325)
  ·
    refine ⟨207538757963666079131311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1106873375806219088700325 207538757963666079131311)
    ·
      refine ⟨311308136945499118696967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207538757963666079131311 311308136945499118696967)
      ·
        refine ⟨466962205418248678045451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311308136945499118696967 466962205418248678045451)
        ·
          refine ⟨700443308127373017068177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466962205418248678045451 700443308127373017068177)
          ·
            refine ⟨525332481095529762801133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 700443308127373017068177 525332481095529762801133)
            ·
              refine ⟨196999680410823661050425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 525332481095529762801133 196999680410823661050425)
              ·
                refine ⟨147749760308117745787819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196999680410823661050425 147749760308117745787819)
                ·
                  refine ⟨221624640462176618681729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147749760308117745787819 221624640462176618681729)
                  ·
                    refine ⟨166218480346632464011297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 221624640462176618681729 166218480346632464011297)
                    ·
                      refine ⟨124663860259974348008473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 166218480346632464011297 124663860259974348008473)
                      ·
                        rfl

theorem cell23_242782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_242782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242782 prefixEnd_242782 := by exact prefixLift 242782
  have htrace : WordTrace (prefixWord ++ tailWord_242782) baseStart_242782 baseEnd_242782 := by
    simpa [prefixWord, tailWord_242782, baseEnd_242782] using wordTrace_append hprefix tailTrace_242782
  have hstable : (prefixWord ++ tailWord_242782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242782).length < 2 ^ (prefixWord ++ tailWord_242782).sum := by decide
  have hdescent : baseEnd_242782 < baseStart_242782 := by decide
  rcases family_descends (prefixWord ++ tailWord_242782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242844 : List Nat := [2, 2, 3, 2, 1, 2, 4, 2, 5]
def baseStart_242844 : Nat := 118140960795 + 242844 * 2 ^ 59
def prefixEnd_242844 : Nat := 4983230072969 + 3 ^ 40 * 242844 * 2
def baseEnd_242844 : Nat := 13855077340061456159243

theorem tailTrace_242844 : CollatzResearch.WordTrace tailWord_242844 prefixEnd_242844 13855077340061456159243 := by
  unfold tailWord_242844
  simp only [CollatzResearch.WordTrace]
  refine ⟨4428624166112568649179793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5904832221483424865573057 4428624166112568649179793)
  ·
    refine ⟨3321468124584426486884845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4428624166112568649179793 3321468124584426486884845)
    ·
      refine ⟨1245550546719159932581817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3321468124584426486884845 1245550546719159932581817)
      ·
        refine ⟨934162910039369949436363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1245550546719159932581817 934162910039369949436363)
        ·
          refine ⟨1401244365059054924154545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 934162910039369949436363 1401244365059054924154545)
          ·
            refine ⟨1050933273794291193115909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1401244365059054924154545 1050933273794291193115909)
            ·
              refine ⟨197049988836429598709233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1050933273794291193115909 197049988836429598709233)
              ·
                refine ⟨147787491627322199031925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197049988836429598709233 147787491627322199031925)
                ·
                  refine ⟨13855077340061456159243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 147787491627322199031925 13855077340061456159243)
                  ·
                    rfl

theorem cell23_242844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 2, 5].length) (baseStart_242844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242844 prefixEnd_242844 := by exact prefixLift 242844
  have htrace : WordTrace (prefixWord ++ tailWord_242844) baseStart_242844 baseEnd_242844 := by
    simpa [prefixWord, tailWord_242844, baseEnd_242844] using wordTrace_append hprefix tailTrace_242844
  have hstable : (prefixWord ++ tailWord_242844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242844).length < 2 ^ (prefixWord ++ tailWord_242844).sum := by decide
  have hdescent : baseEnd_242844 < baseStart_242844 := by decide
  rcases family_descends (prefixWord ++ tailWord_242844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242877 : List Nat := [1, 4, 1, 2, 1, 1, 5, 1, 2, 1, 4]
def baseStart_242877 : Nat := 118140960795 + 242877 * 2 ^ 59
def prefixEnd_242877 : Nat := 4983230072969 + 3 ^ 40 * 242877 * 2
def baseEnd_242877 : Nat := 124712640922151476320535

theorem tailTrace_242877 : CollatzResearch.WordTrace tailWord_242877 prefixEnd_242877 124712640922151476320535 := by
  unfold tailWord_242877
  simp only [CollatzResearch.WordTrace]
  refine ⟨8858451941105583934310885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5905634627403722622873923 8858451941105583934310885)
  ·
    refine ⟨1660959738957296987683291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8858451941105583934310885 1660959738957296987683291)
    ·
      refine ⟨2491439608435945481524937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1660959738957296987683291 2491439608435945481524937)
      ·
        refine ⟨1868579706326959111143703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2491439608435945481524937 1868579706326959111143703)
        ·
          refine ⟨2802869559490438666715555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1868579706326959111143703 2802869559490438666715555)
          ·
            refine ⟨4204304339235658000073333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2802869559490438666715555 4204304339235658000073333)
            ·
              refine ⟨394153531803342937506875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4204304339235658000073333 394153531803342937506875)
              ·
                refine ⟨591230297705014406260313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 394153531803342937506875 591230297705014406260313)
                ·
                  refine ⟨443422723278760804695235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 591230297705014406260313 443422723278760804695235)
                  ·
                    refine ⟨665134084918141207042853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 443422723278760804695235 665134084918141207042853)
                    ·
                      refine ⟨124712640922151476320535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 665134084918141207042853 124712640922151476320535)
                      ·
                        rfl

theorem cell23_242877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_242877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242877 prefixEnd_242877 := by exact prefixLift 242877
  have htrace : WordTrace (prefixWord ++ tailWord_242877) baseStart_242877 baseEnd_242877 := by
    simpa [prefixWord, tailWord_242877, baseEnd_242877] using wordTrace_append hprefix tailTrace_242877
  have hstable : (prefixWord ++ tailWord_242877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242877).length < 2 ^ (prefixWord ++ tailWord_242877).sum := by decide
  have hdescent : baseEnd_242877 < baseStart_242877 := by decide
  rcases family_descends (prefixWord ++ tailWord_242877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242890 : List Nat := [3, 1, 2, 1, 3, 2, 1, 1, 2, 1, 6]
def baseStart_242890 : Nat := 118140960795 + 242890 * 2 ^ 59
def prefixEnd_242890 : Nat := 4983230072969 + 3 ^ 40 * 242890 * 2
def baseEnd_242890 : Nat := 124719316170659925457975

theorem tailTrace_242890 : CollatzResearch.WordTrace tailWord_242890 prefixEnd_242890 124719316170659925457975 := by
  unfold tailWord_242890
  simp only [CollatzResearch.WordTrace]
  refine ⟨2214731522514621788633531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5905950726705658103022749 2214731522514621788633531)
  ·
    refine ⟨3322097283771932682950297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2214731522514621788633531 3322097283771932682950297)
    ·
      refine ⟨2491572962828949512212723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3322097283771932682950297 2491572962828949512212723)
      ·
        refine ⟨3737359444243424268319085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2491572962828949512212723 3737359444243424268319085)
        ·
          refine ⟨1401509791591284100619657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3737359444243424268319085 1401509791591284100619657)
          ·
            refine ⟨1051132343693463075464743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1401509791591284100619657 1051132343693463075464743)
            ·
              refine ⟨1576698515540194613197115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1051132343693463075464743 1576698515540194613197115)
              ·
                refine ⟨2365047773310291919795673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1576698515540194613197115 2365047773310291919795673)
                ·
                  refine ⟨1773785829982718939846755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2365047773310291919795673 1773785829982718939846755)
                  ·
                    refine ⟨2660678744974078409770133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1773785829982718939846755 2660678744974078409770133)
                    ·
                      refine ⟨124719316170659925457975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2660678744974078409770133 124719316170659925457975)
                      ·
                        rfl

theorem cell23_242890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_242890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242890 prefixEnd_242890 := by exact prefixLift 242890
  have htrace : WordTrace (prefixWord ++ tailWord_242890) baseStart_242890 baseEnd_242890 := by
    simpa [prefixWord, tailWord_242890, baseEnd_242890] using wordTrace_append hprefix tailTrace_242890
  have hstable : (prefixWord ++ tailWord_242890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242890).length < 2 ^ (prefixWord ++ tailWord_242890).sum := by decide
  have hdescent : baseEnd_242890 < baseStart_242890 := by decide
  rcases family_descends (prefixWord ++ tailWord_242890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242904 : List Nat := [2, 1, 2, 2, 5, 1, 2, 1, 3, 4]
def baseStart_242904 : Nat := 118140960795 + 242904 * 2 ^ 59
def prefixEnd_242904 : Nat := 4983230072969 + 3 ^ 40 * 242904 * 2
def baseEnd_242904 : Nat := 41575501633274290227637

theorem tailTrace_242904 : CollatzResearch.WordTrace tailWord_242904 prefixEnd_242904 41575501633274290227637 := by
  unfold tailWord_242904
  simp only [CollatzResearch.WordTrace]
  refine ⟨4429718356003883772771883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5906291141338511697029177 4429718356003883772771883)
  ·
    refine ⟨6644577534005825659157825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4429718356003883772771883 6644577534005825659157825)
    ·
      refine ⟨4983433150504369244368369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6644577534005825659157825 4983433150504369244368369)
      ·
        refine ⟨3737574862878276933276277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4983433150504369244368369 3737574862878276933276277)
        ·
          refine ⟨350397643394838462494651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3737574862878276933276277 350397643394838462494651)
          ·
            refine ⟨525596465092257693741977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350397643394838462494651 525596465092257693741977)
            ·
              refine ⟨394197348819193270306483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 525596465092257693741977 394197348819193270306483)
              ·
                refine ⟨591296023228789905459725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 394197348819193270306483 591296023228789905459725)
                ·
                  refine ⟨221736008710796214547397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 591296023228789905459725 221736008710796214547397)
                  ·
                    refine ⟨41575501633274290227637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 221736008710796214547397 41575501633274290227637)
                    ·
                      rfl

theorem cell23_242904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 3, 4].length) (baseStart_242904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242904 prefixEnd_242904 := by exact prefixLift 242904
  have htrace : WordTrace (prefixWord ++ tailWord_242904) baseStart_242904 baseEnd_242904 := by
    simpa [prefixWord, tailWord_242904, baseEnd_242904] using wordTrace_append hprefix tailTrace_242904
  have hstable : (prefixWord ++ tailWord_242904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242904).length < 2 ^ (prefixWord ++ tailWord_242904).sum := by decide
  have hdescent : baseEnd_242904 < baseStart_242904 := by decide
  rcases family_descends (prefixWord ++ tailWord_242904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242920 : List Nat := [2, 1, 4, 1, 2, 1, 1, 2, 1, 2, 6]
def baseStart_242920 : Nat := 118140960795 + 242920 * 2 ^ 59
def prefixEnd_242920 : Nat := 4983230072969 + 3 ^ 40 * 242920 * 2
def baseEnd_242920 : Nat := 124734720590294808082837

theorem tailTrace_242920 : CollatzResearch.WordTrace tailWord_242920 prefixEnd_242920 124734720590294808082837 := by
  unfold tailWord_242920
  simp only [CollatzResearch.WordTrace]
  refine ⟨4430010139974901139063107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5906680186633201518750809 4430010139974901139063107)
  ·
    refine ⟨6645015209962351708594661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4430010139974901139063107 6645015209962351708594661)
    ·
      refine ⟨1245940351867940945361499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6645015209962351708594661 1245940351867940945361499)
      ·
        refine ⟨1868910527801911418042249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1245940351867940945361499 1868910527801911418042249)
        ·
          refine ⟨1401682895851433563531687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1868910527801911418042249 1401682895851433563531687)
          ·
            refine ⟨2102524343777150345297531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1401682895851433563531687 2102524343777150345297531)
            ·
              refine ⟨3153786515665725517946297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2102524343777150345297531 3153786515665725517946297)
              ·
                refine ⟨2365339886749294138459723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3153786515665725517946297 2365339886749294138459723)
                ·
                  refine ⟨3548009830123941207689585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2365339886749294138459723 3548009830123941207689585)
                  ·
                    refine ⟨2661007372592955905767189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3548009830123941207689585 2661007372592955905767189)
                    ·
                      refine ⟨124734720590294808082837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2661007372592955905767189 124734720590294808082837)
                      ·
                        rfl

theorem cell23_242920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_242920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242920 prefixEnd_242920 := by exact prefixLift 242920
  have htrace : WordTrace (prefixWord ++ tailWord_242920) baseStart_242920 baseEnd_242920 := by
    simpa [prefixWord, tailWord_242920, baseEnd_242920] using wordTrace_append hprefix tailTrace_242920
  have hstable : (prefixWord ++ tailWord_242920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242920).length < 2 ^ (prefixWord ++ tailWord_242920).sum := by decide
  have hdescent : baseEnd_242920 < baseStart_242920 := by decide
  rcases family_descends (prefixWord ++ tailWord_242920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242937 : List Nat := [1, 2, 1, 3, 1, 1, 3, 3, 1, 5, 2]
def baseStart_242937 : Nat := 118140960795 + 242937 * 2 ^ 59
def prefixEnd_242937 : Nat := 4983230072969 + 3 ^ 40 * 242937 * 2
def baseEnd_242937 : Nat := 124743449761421241570259

theorem tailTrace_242937 : CollatzResearch.WordTrace tailWord_242937 prefixEnd_242937 124743449761421241570259 := by
  unfold tailWord_242937
  simp only [CollatzResearch.WordTrace]
  refine ⟨8860640320888214181495065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5907093547258809454330043 8860640320888214181495065)
  ·
    refine ⟨6645480240666160636121299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8860640320888214181495065 6645480240666160636121299)
    ·
      refine ⟨9968220360999240954181949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6645480240666160636121299 9968220360999240954181949)
      ·
        refine ⟨3738082635374715357818231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9968220360999240954181949 3738082635374715357818231)
        ·
          refine ⟨5607123953062073036727347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3738082635374715357818231 5607123953062073036727347)
          ·
            refine ⟨8410685929593109555091021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5607123953062073036727347 8410685929593109555091021)
            ·
              refine ⟨3154007223597416083159133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8410685929593109555091021 3154007223597416083159133)
              ·
                refine ⟨1182752708849031031184675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3154007223597416083159133 1182752708849031031184675)
                ·
                  refine ⟨1774129063273546546777013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1182752708849031031184675 1774129063273546546777013)
                  ·
                    refine ⟨166324599681894988760345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1774129063273546546777013 166324599681894988760345)
                    ·
                      refine ⟨124743449761421241570259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 166324599681894988760345 124743449761421241570259)
                      ·
                        rfl

theorem cell23_242937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 5, 2].length) (baseStart_242937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242937 prefixEnd_242937 := by exact prefixLift 242937
  have htrace : WordTrace (prefixWord ++ tailWord_242937) baseStart_242937 baseEnd_242937 := by
    simpa [prefixWord, tailWord_242937, baseEnd_242937] using wordTrace_append hprefix tailTrace_242937
  have hstable : (prefixWord ++ tailWord_242937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242937).length < 2 ^ (prefixWord ++ tailWord_242937).sum := by decide
  have hdescent : baseEnd_242937 < baseStart_242937 := by decide
  rcases family_descends (prefixWord ++ tailWord_242937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242947 : List Nat := [1, 1, 1, 3, 2, 4, 2, 3, 1, 5]
def baseStart_242947 : Nat := 118140960795 + 242947 * 2 ^ 59
def prefixEnd_242947 : Nat := 4983230072969 + 3 ^ 40 * 242947 * 2
def baseEnd_242947 : Nat := 41582861522655400815071

theorem tailTrace_242947 : CollatzResearch.WordTrace tailWord_242947 prefixEnd_242947 41582861522655400815071 := by
  unfold tailWord_242947
  simp only [CollatzResearch.WordTrace]
  refine ⟨8861005050851985889359095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5907336700567990592906063 8861005050851985889359095)
  ·
    refine ⟨13291507576277978834038643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8861005050851985889359095 13291507576277978834038643)
    ·
      refine ⟨19937261364416968251057965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13291507576277978834038643 19937261364416968251057965)
      ·
        refine ⟨7476473011656363094146737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19937261364416968251057965 7476473011656363094146737)
        ·
          refine ⟨5607354758742272320610053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7476473011656363094146737 5607354758742272320610053)
          ·
            refine ⟨1051379017264176060114385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5607354758742272320610053 1051379017264176060114385)
            ·
              refine ⟨788534262948132045085789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1051379017264176060114385 788534262948132045085789)
              ·
                refine ⟨295700348605549516907171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 788534262948132045085789 295700348605549516907171)
                ·
                  refine ⟨443550522908324275360757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 295700348605549516907171 443550522908324275360757)
                  ·
                    refine ⟨41582861522655400815071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 443550522908324275360757 41582861522655400815071)
                    ·
                      rfl

theorem cell23_242947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3, 1, 5].length) (baseStart_242947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242947 prefixEnd_242947 := by exact prefixLift 242947
  have htrace : WordTrace (prefixWord ++ tailWord_242947) baseStart_242947 baseEnd_242947 := by
    simpa [prefixWord, tailWord_242947, baseEnd_242947] using wordTrace_append hprefix tailTrace_242947
  have hstable : (prefixWord ++ tailWord_242947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242947).length < 2 ^ (prefixWord ++ tailWord_242947).sum := by decide
  have hdescent : baseEnd_242947 < baseStart_242947 := by decide
  rcases family_descends (prefixWord ++ tailWord_242947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242967 : List Nat := [1, 1, 3, 4, 1, 1, 2, 2, 3, 1, 4]
def baseStart_242967 : Nat := 118140960795 + 242967 * 2 ^ 59
def prefixEnd_242967 : Nat := 4983230072969 + 3 ^ 40 * 242967 * 2
def baseEnd_242967 : Nat := 124758854181056124195121

theorem tailTrace_242967 : CollatzResearch.WordTrace tailWord_242967 prefixEnd_242967 124758854181056124195121 := by
  unfold tailWord_242967
  simp only [CollatzResearch.WordTrace]
  refine ⟨8861734510779529305087155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5907823007186352870058103 8861734510779529305087155)
  ·
    refine ⟨13292601766169293957630733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8861734510779529305087155 13292601766169293957630733)
    ·
      refine ⟨4984725662313485234111525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13292601766169293957630733 4984725662313485234111525)
      ·
        refine ⟨934636061683778481395911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4984725662313485234111525 934636061683778481395911)
        ·
          refine ⟨1401954092525667722093867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 934636061683778481395911 1401954092525667722093867)
          ·
            refine ⟨2102931138788501583140801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1401954092525667722093867 2102931138788501583140801)
            ·
              refine ⟨1577198354091376187355601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2102931138788501583140801 1577198354091376187355601)
              ·
                refine ⟨1182898765568532140516701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1577198354091376187355601 1182898765568532140516701)
                ·
                  refine ⟨443587037088199552693763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1182898765568532140516701 443587037088199552693763)
                  ·
                    refine ⟨665380555632299329040645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 443587037088199552693763 665380555632299329040645)
                    ·
                      refine ⟨124758854181056124195121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 665380555632299329040645 124758854181056124195121)
                      ·
                        rfl

theorem cell23_242967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_242967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242967 prefixEnd_242967 := by exact prefixLift 242967
  have htrace : WordTrace (prefixWord ++ tailWord_242967) baseStart_242967 baseEnd_242967 := by
    simpa [prefixWord, tailWord_242967, baseEnd_242967] using wordTrace_append hprefix tailTrace_242967
  have hstable : (prefixWord ++ tailWord_242967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242967).length < 2 ^ (prefixWord ++ tailWord_242967).sum := by decide
  have hdescent : baseEnd_242967 < baseStart_242967 := by decide
  rcases family_descends (prefixWord ++ tailWord_242967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242984 : List Nat := [2, 1, 5, 1, 2, 2, 1, 1, 3, 1, 4]
def baseStart_242984 : Nat := 118140960795 + 242984 * 2 ^ 59
def prefixEnd_242984 : Nat := 4983230072969 + 3 ^ 40 * 242984 * 2
def baseEnd_242984 : Nat := 124767583352182557682543

theorem tailTrace_242984 : CollatzResearch.WordTrace tailWord_242984 prefixEnd_242984 124767583352182557682543 := by
  unfold tailWord_242984
  simp only [CollatzResearch.WordTrace]
  refine ⟨4431177275858970604228003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5908236367811960805637337 4431177275858970604228003)
  ·
    refine ⟨6646765913788455906342005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4431177275858970604228003 6646765913788455906342005)
    ·
      refine ⟨623134304417667741219563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6646765913788455906342005 623134304417667741219563)
      ·
        refine ⟨934701456626501611829345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 623134304417667741219563 934701456626501611829345)
        ·
          refine ⟨701026092469876208872009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 934701456626501611829345 701026092469876208872009)
          ·
            refine ⟨525769569352407156654007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 701026092469876208872009 525769569352407156654007)
            ·
              refine ⟨788654354028610734981011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 525769569352407156654007 788654354028610734981011)
              ·
                refine ⟨1182981531042916102471517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 788654354028610734981011 1182981531042916102471517)
                ·
                  refine ⟨443618074141093538426819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1182981531042916102471517 443618074141093538426819)
                  ·
                    refine ⟨665427111211640307640229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 443618074141093538426819 665427111211640307640229)
                    ·
                      refine ⟨124767583352182557682543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 665427111211640307640229 124767583352182557682543)
                      ·
                        rfl

theorem cell23_242984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_242984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242984 prefixEnd_242984 := by exact prefixLift 242984
  have htrace : WordTrace (prefixWord ++ tailWord_242984) baseStart_242984 baseEnd_242984 := by
    simpa [prefixWord, tailWord_242984, baseEnd_242984] using wordTrace_append hprefix tailTrace_242984
  have hstable : (prefixWord ++ tailWord_242984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242984).length < 2 ^ (prefixWord ++ tailWord_242984).sum := by decide
  have hdescent : baseEnd_242984 < baseStart_242984 := by decide
  rcases family_descends (prefixWord ++ tailWord_242984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242997 : List Nat := [1, 3, 3, 1, 2, 2, 1, 1, 3, 2, 4]
def baseStart_242997 : Nat := 118140960795 + 242997 * 2 ^ 59
def prefixEnd_242997 : Nat := 4983230072969 + 3 ^ 40 * 242997 * 2
def baseEnd_242997 : Nat := 124774258600691006819983

theorem tailTrace_242997 : CollatzResearch.WordTrace tailWord_242997 prefixEnd_242997 124774258600691006819983 := by
  unfold tailWord_242997
  simp only [CollatzResearch.WordTrace]
  refine ⟨8862828700670844428679245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5908552467113896285786163 8862828700670844428679245)
  ·
    refine ⟨3323560762751566660754717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8862828700670844428679245 3323560762751566660754717)
    ·
      refine ⟨1246335286031837497783019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3323560762751566660754717 1246335286031837497783019)
      ·
        refine ⟨1869502929047756246674529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1246335286031837497783019 1869502929047756246674529)
        ·
          refine ⟨1402127196785817185005897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1869502929047756246674529 1402127196785817185005897)
          ·
            refine ⟨1051595397589362888754423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1402127196785817185005897 1051595397589362888754423)
            ·
              refine ⟨1577393096384044333131635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1051595397589362888754423 1577393096384044333131635)
              ·
                refine ⟨2366089644576066499697453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1577393096384044333131635 2366089644576066499697453)
                ·
                  refine ⟨887283616716024937386545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2366089644576066499697453 887283616716024937386545)
                  ·
                    refine ⟨665462712537018703039909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 887283616716024937386545 665462712537018703039909)
                    ·
                      refine ⟨124774258600691006819983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 665462712537018703039909 124774258600691006819983)
                      ·
                        rfl

theorem cell23_242997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_242997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_242997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_242997 prefixEnd_242997 := by exact prefixLift 242997
  have htrace : WordTrace (prefixWord ++ tailWord_242997) baseStart_242997 baseEnd_242997 := by
    simpa [prefixWord, tailWord_242997, baseEnd_242997] using wordTrace_append hprefix tailTrace_242997
  have hstable : (prefixWord ++ tailWord_242997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242997).length < 2 ^ (prefixWord ++ tailWord_242997).sum := by decide
  have hdescent : baseEnd_242997 < baseStart_242997 := by decide
  rcases family_descends (prefixWord ++ tailWord_242997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243004 : List Nat := [2, 2, 2, 2, 1, 5, 1, 1, 1, 1, 5]
def baseStart_243004 : Nat := 118140960795 + 243004 * 2 ^ 59
def prefixEnd_243004 : Nat := 4983230072969 + 3 ^ 40 * 243004 * 2
def baseEnd_243004 : Nat := 124777852965272479432451

theorem tailTrace_243004 : CollatzResearch.WordTrace tailWord_243004 prefixEnd_243004 124777852965272479432451 := by
  unfold tailWord_243004
  simp only [CollatzResearch.WordTrace]
  refine ⟨4431542005822742312092033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5908722674430323082789377 4431542005822742312092033)
  ·
    refine ⟨3323656504367056734069025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4431542005822742312092033 3323656504367056734069025)
    ·
      refine ⟨2492742378275292550551769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3323656504367056734069025 2492742378275292550551769)
      ·
        refine ⟨1869556783706469412913827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2492742378275292550551769 1869556783706469412913827)
        ·
          refine ⟨2804335175559704119370741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1869556783706469412913827 2804335175559704119370741)
          ·
            refine ⟨262906422708722261191007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2804335175559704119370741 262906422708722261191007)
            ·
              refine ⟨394359634063083391786511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262906422708722261191007 394359634063083391786511)
              ·
                refine ⟨591539451094625087679767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 394359634063083391786511 591539451094625087679767)
                ·
                  refine ⟨887309176641937631519651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 591539451094625087679767 887309176641937631519651)
                  ·
                    refine ⟨1330963764962906447279477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 887309176641937631519651 1330963764962906447279477)
                    ·
                      refine ⟨124777852965272479432451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1330963764962906447279477 124777852965272479432451)
                      ·
                        rfl

theorem cell23_243004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_243004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243004 prefixEnd_243004 := by exact prefixLift 243004
  have htrace : WordTrace (prefixWord ++ tailWord_243004) baseStart_243004 baseEnd_243004 := by
    simpa [prefixWord, tailWord_243004, baseEnd_243004] using wordTrace_append hprefix tailTrace_243004
  have hstable : (prefixWord ++ tailWord_243004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243004).length < 2 ^ (prefixWord ++ tailWord_243004).sum := by decide
  have hdescent : baseEnd_243004 < baseStart_243004 := by decide
  rcases family_descends (prefixWord ++ tailWord_243004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243012 : List Nat := [2, 3, 4, 1, 1, 3, 2, 2, 1, 1, 3]
def baseStart_243012 : Nat := 118140960795 + 243012 * 2 ^ 59
def prefixEnd_243012 : Nat := 4983230072969 + 3 ^ 40 * 243012 * 2
def baseEnd_243012 : Nat := 124781960810508448132415

theorem tailTrace_243012 : CollatzResearch.WordTrace tailWord_243012 prefixEnd_243012 124781960810508448132415 := by
  unfold tailWord_243012
  simp only [CollatzResearch.WordTrace]
  refine ⟨4431687897808250995237645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5908917197077667993650193 4431687897808250995237645)
  ·
    refine ⟨1661882961678094123214117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4431687897808250995237645 1661882961678094123214117)
    ·
      refine ⟨311603055314642648102647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1661882961678094123214117 311603055314642648102647)
      ·
        refine ⟨467404582971963972153971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311603055314642648102647 467404582971963972153971)
        ·
          refine ⟨701106874457945958230957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467404582971963972153971 701106874457945958230957)
          ·
            refine ⟨262915077921729734336609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 701106874457945958230957 262915077921729734336609)
            ·
              refine ⟨197186308441297300752457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262915077921729734336609 197186308441297300752457)
              ·
                refine ⟨147889731330972975564343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197186308441297300752457 147889731330972975564343)
                ·
                  refine ⟨221834596996459463346515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147889731330972975564343 221834596996459463346515)
                  ·
                    refine ⟨332751895494689195019773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 221834596996459463346515 332751895494689195019773)
                    ·
                      refine ⟨124781960810508448132415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 332751895494689195019773 124781960810508448132415)
                      ·
                        rfl

theorem cell23_243012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_243012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243012 prefixEnd_243012 := by exact prefixLift 243012
  have htrace : WordTrace (prefixWord ++ tailWord_243012) baseStart_243012 baseEnd_243012 := by
    simpa [prefixWord, tailWord_243012, baseEnd_243012] using wordTrace_append hprefix tailTrace_243012
  have hstable : (prefixWord ++ tailWord_243012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243012).length < 2 ^ (prefixWord ++ tailWord_243012).sum := by decide
  have hdescent : baseEnd_243012 < baseStart_243012 := by decide
  rcases family_descends (prefixWord ++ tailWord_243012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243077 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 1, 6, 3]
def baseStart_243077 : Nat := 118140960795 + 243077 * 2 ^ 59
def prefixEnd_243077 : Nat := 4983230072969 + 3 ^ 40 * 243077 * 2
def baseEnd_243077 : Nat := 124815337053050693819615

theorem tailTrace_243077 : CollatzResearch.WordTrace tailWord_243077 prefixEnd_243077 124815337053050693819615 := by
  unfold tailWord_243077
  simp only [CollatzResearch.WordTrace]
  refine ⟨8865746540381018091591485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5910497693587345394394323 8865746540381018091591485)
  ·
    refine ⟨3324654952642881784346807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8865746540381018091591485 3324654952642881784346807)
    ·
      refine ⟨4986982428964322676520211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3324654952642881784346807 4986982428964322676520211)
      ·
        refine ⟨7480473643446484014780317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4986982428964322676520211 7480473643446484014780317)
        ·
          refine ⟨2805177616292431505542619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7480473643446484014780317 2805177616292431505542619)
          ·
            refine ⟨4207766424438647258313929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2805177616292431505542619 4207766424438647258313929)
            ·
              refine ⟨3155824818328985443735447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4207766424438647258313929 3155824818328985443735447)
              ·
                refine ⟨4733737227493478165603171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3155824818328985443735447 4733737227493478165603171)
                ·
                  refine ⟨7100605841240217248404757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4733737227493478165603171 7100605841240217248404757)
                  ·
                    refine ⟨332840898808135183518973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7100605841240217248404757 332840898808135183518973)
                    ·
                      refine ⟨124815337053050693819615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 332840898808135183518973 124815337053050693819615)
                      ·
                        rfl

theorem cell23_243077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 6, 3].length) (baseStart_243077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243077 prefixEnd_243077 := by exact prefixLift 243077
  have htrace : WordTrace (prefixWord ++ tailWord_243077) baseStart_243077 baseEnd_243077 := by
    simpa [prefixWord, tailWord_243077, baseEnd_243077] using wordTrace_append hprefix tailTrace_243077
  have hstable : (prefixWord ++ tailWord_243077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243077).length < 2 ^ (prefixWord ++ tailWord_243077).sum := by decide
  have hdescent : baseEnd_243077 < baseStart_243077 := by decide
  rcases family_descends (prefixWord ++ tailWord_243077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243097 : List Nat := [1, 2, 1, 2, 1, 5, 2, 2, 7]
def baseStart_243097 : Nat := 118140960795 + 243097 * 2 ^ 59
def prefixEnd_243097 : Nat := 4983230072969 + 3 ^ 40 * 243097 * 2
def baseEnd_243097 : Nat := 13869511851793401729947

theorem tailTrace_243097 : CollatzResearch.WordTrace tailWord_243097 prefixEnd_243097 13869511851793401729947 := by
  unfold tailWord_243097
  simp only [CollatzResearch.WordTrace]
  refine ⟨8866476000308561507319545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5910984000205707671546363 8866476000308561507319545)
  ·
    refine ⟨6649857000231421130489659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8866476000308561507319545 6649857000231421130489659)
    ·
      refine ⟨9974785500347131695734489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6649857000231421130489659 9974785500347131695734489)
      ·
        refine ⟨7481089125260348771800867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9974785500347131695734489 7481089125260348771800867)
        ·
          refine ⟨11221633687890523157701301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7481089125260348771800867 11221633687890523157701301)
          ·
            refine ⟨1052028158239736546034497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11221633687890523157701301 1052028158239736546034497)
            ·
              refine ⟨789021118679802409525873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1052028158239736546034497 789021118679802409525873)
              ·
                refine ⟨591765839009851807144405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 789021118679802409525873 591765839009851807144405)
                ·
                  refine ⟨13869511851793401729947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 591765839009851807144405 13869511851793401729947)
                  ·
                    rfl

theorem cell23_243097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 7].length) (baseStart_243097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243097 prefixEnd_243097 := by exact prefixLift 243097
  have htrace : WordTrace (prefixWord ++ tailWord_243097) baseStart_243097 baseEnd_243097 := by
    simpa [prefixWord, tailWord_243097, baseEnd_243097] using wordTrace_append hprefix tailTrace_243097
  have hstable : (prefixWord ++ tailWord_243097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243097).length < 2 ^ (prefixWord ++ tailWord_243097).sum := by decide
  have hdescent : baseEnd_243097 < baseStart_243097 := by decide
  rcases family_descends (prefixWord ++ tailWord_243097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243147 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 3, 3, 4]
def baseStart_243147 : Nat := 118140960795 + 243147 * 2 ^ 59
def prefixEnd_243147 : Nat := 4983230072969 + 3 ^ 40 * 243147 * 2
def baseEnd_243147 : Nat := 124851280698865419944293

theorem tailTrace_243147 : CollatzResearch.WordTrace tailWord_243147 prefixEnd_243147 124851280698865419944293 := by
  unfold tailWord_243147
  simp only [CollatzResearch.WordTrace]
  refine ⟨8868299650127420046639695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5912199766751613364426463 8868299650127420046639695)
  ·
    refine ⟨13302449475191130069959543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8868299650127420046639695 13302449475191130069959543)
    ·
      refine ⟨19953674212786695104939315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13302449475191130069959543 19953674212786695104939315)
      ·
        refine ⟨29930511319180042657408973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19953674212786695104939315 29930511319180042657408973)
        ·
          refine ⟨11223941744692515996528365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29930511319180042657408973 11223941744692515996528365)
          ·
            refine ⟨4208978154259693498698137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11223941744692515996528365 4208978154259693498698137)
            ·
              refine ⟨3156733615694770124023603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4208978154259693498698137 3156733615694770124023603)
              ·
                refine ⟨4735100423542155186035405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3156733615694770124023603 4735100423542155186035405)
                ·
                  refine ⟨1775662658828308194763277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4735100423542155186035405 1775662658828308194763277)
                  ·
                    refine ⟨665873497060615573036229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1775662658828308194763277 665873497060615573036229)
                    ·
                      refine ⟨124851280698865419944293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 665873497060615573036229 124851280698865419944293)
                      ·
                        rfl

theorem cell23_243147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3, 4].length) (baseStart_243147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243147 prefixEnd_243147 := by exact prefixLift 243147
  have htrace : WordTrace (prefixWord ++ tailWord_243147) baseStart_243147 baseEnd_243147 := by
    simpa [prefixWord, tailWord_243147, baseEnd_243147] using wordTrace_append hprefix tailTrace_243147
  have hstable : (prefixWord ++ tailWord_243147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243147).length < 2 ^ (prefixWord ++ tailWord_243147).sum := by decide
  have hdescent : baseEnd_243147 < baseStart_243147 := by decide
  rcases family_descends (prefixWord ++ tailWord_243147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243177 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 4, 4, 4]
def baseStart_243177 : Nat := 118140960795 + 243177 * 2 ^ 59
def prefixEnd_243177 : Nat := 4983230072969 + 3 ^ 40 * 243177 * 2
def baseEnd_243177 : Nat := 124866685118500302569155

theorem tailTrace_243177 : CollatzResearch.WordTrace tailWord_243177 prefixEnd_243177 124866685118500302569155 := by
  unfold tailWord_243177
  simp only [CollatzResearch.WordTrace]
  refine ⟨8869393840018735170231785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5912929226679156780154523 8869393840018735170231785)
  ·
    refine ⟨6652045380014051377673839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8869393840018735170231785 6652045380014051377673839)
    ·
      refine ⟨9978068070021077066510759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6652045380014051377673839 9978068070021077066510759)
      ·
        refine ⟨14967102105031615599766139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9978068070021077066510759 14967102105031615599766139)
        ·
          refine ⟨22450653157547423399649209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14967102105031615599766139 22450653157547423399649209)
          ·
            refine ⟨16837989868160567549736907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22450653157547423399649209 16837989868160567549736907)
            ·
              refine ⟨25256984802240851324605361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16837989868160567549736907 25256984802240851324605361)
              ·
                refine ⟨18942738601680638493454021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25256984802240851324605361 18942738601680638493454021)
                ·
                  refine ⟨3551763487815119717522629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18942738601680638493454021 3551763487815119717522629)
                  ·
                    refine ⟨665955653965334947035493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3551763487815119717522629 665955653965334947035493)
                    ·
                      refine ⟨124866685118500302569155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 665955653965334947035493 124866685118500302569155)
                      ·
                        rfl

theorem cell23_243177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 4, 4].length) (baseStart_243177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243177 prefixEnd_243177 := by exact prefixLift 243177
  have htrace : WordTrace (prefixWord ++ tailWord_243177) baseStart_243177 baseEnd_243177 := by
    simpa [prefixWord, tailWord_243177, baseEnd_243177] using wordTrace_append hprefix tailTrace_243177
  have hstable : (prefixWord ++ tailWord_243177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243177).length < 2 ^ (prefixWord ++ tailWord_243177).sum := by decide
  have hdescent : baseEnd_243177 < baseStart_243177 := by decide
  rcases family_descends (prefixWord ++ tailWord_243177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243247 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 1, 12]
def baseStart_243247 : Nat := 118140960795 + 243247 * 2 ^ 59
def prefixEnd_243247 : Nat := 4983230072969 + 3 ^ 40 * 243247 * 2
def baseEnd_243247 : Nat := 41634209588105009564611

theorem tailTrace_243247 : CollatzResearch.WordTrace tailWord_243247 prefixEnd_243247 41634209588105009564611 := by
  unfold tailWord_243247
  simp only [CollatzResearch.WordTrace]
  refine ⟨8871946949765137125279995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5914631299843424750186663 8871946949765137125279995)
  ·
    refine ⟨13307920424647705687919993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8871946949765137125279995 13307920424647705687919993)
    ·
      refine ⟨9980940318485779265939995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13307920424647705687919993 9980940318485779265939995)
      ·
        refine ⟨14971410477728668898909993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9980940318485779265939995 14971410477728668898909993)
        ·
          refine ⟨11228557858296501674182495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14971410477728668898909993 11228557858296501674182495)
          ·
            refine ⟨16842836787444752511273743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11228557858296501674182495 16842836787444752511273743)
            ·
              refine ⟨25264255181167128766910615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16842836787444752511273743 25264255181167128766910615)
              ·
                refine ⟨37896382771750693150365923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25264255181167128766910615 37896382771750693150365923)
                ·
                  refine ⟨56844574157626039725548885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37896382771750693150365923 56844574157626039725548885)
                  ·
                    refine ⟨41634209588105009564611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 56844574157626039725548885 41634209588105009564611)
                    ·
                      rfl

theorem cell23_243247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 12].length) (baseStart_243247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_243247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_243247 prefixEnd_243247 := by exact prefixLift 243247
  have htrace : WordTrace (prefixWord ++ tailWord_243247) baseStart_243247 baseEnd_243247 := by
    simpa [prefixWord, tailWord_243247, baseEnd_243247] using wordTrace_append hprefix tailTrace_243247
  have hstable : (prefixWord ++ tailWord_243247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243247).length < 2 ^ (prefixWord ++ tailWord_243247).sum := by decide
  have hdescent : baseEnd_243247 < baseStart_243247 := by decide
  rcases family_descends (prefixWord ++ tailWord_243247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
